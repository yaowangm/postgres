#!/usr/bin/env bash
set -Eeuo pipefail

action=${1:-status}
cpu=${2:-2}
nominal_khz=${NOMINAL_KHZ:-2000000}
housekeeping_cpus=${HOUSEKEEPING_CPUS:-0-1,3-11}
state_dir=/var/tmp/mksort_benchmark_cpu_${cpu}
cpufreq=/sys/devices/system/cpu/cpu${cpu}/cpufreq
amd_pstate_status=/sys/devices/system/cpu/amd_pstate/status
benchmark_pstate_mode=${BENCHMARK_PSTATE_MODE:-passive}
lock_file=/var/lock/mksort_benchmark_cpu_${cpu}.lock

trap 'status=$?; printf "worker_cpu_id=%s\n" "$cpu" >&2; printf "ERROR: command failed (exit=%d, line=%d): %s\n" "$status" "$LINENO" "$BASH_COMMAND" >&2; exit "$status"' ERR

require_root()
{
	if ((EUID != 0)); then
		printf 'worker_cpu_id=%s\n' "$cpu" >&2
		echo "run with sudo: sudo $0 $action $cpu" >&2
		exit 1
	fi
}

lock_state()
{
	exec 9>"$lock_file"
	flock 9
}

save_once()
{
	local path=$1 value=$2
	[[ -f "$path" ]] || printf '%s\n' "$value" >"$path"
}

cpu_list_contains()
{
	local needle=$1 list=$2 part first last
	local -a parts

	IFS=',' read -r -a parts <<<"$list"
	for part in "${parts[@]}"; do
		first=${part%%-*}
		if [[ "$part" == *-* ]]; then
			last=${part##*-}
		else
			last=$first
		fi
		if ((needle >= first && needle <= last)); then
			return 0
		fi
	done
	return 1
}

cpu_list_mask()
{
	python3 - "$1" <<'PY'
import sys
mask = 0
for part in sys.argv[1].split(","):
    bounds = [int(v) for v in part.split("-")]
    for cpu in range(bounds[0], bounds[-1] + 1):
        mask |= 1 << cpu
print(f"{mask:x}")
PY
}

show()
{
	printf 'worker_cpu_id=%s\n' "$cpu"
	printf 'governor='; cat "$cpufreq/scaling_governor"
	printf 'min_freq='; cat "$cpufreq/scaling_min_freq"
	printf 'max_freq='; cat "$cpufreq/scaling_max_freq"
	if [[ -f "$cpufreq/energy_performance_preference" ]]; then
		printf 'epp='; cat "$cpufreq/energy_performance_preference"
	fi
	if [[ -f "$amd_pstate_status" ]]; then
		printf 'amd_pstate_mode='; cat "$amd_pstate_status"
	fi
	printf 'scaling_driver='; cat "$cpufreq/scaling_driver"
	if [[ -f /sys/devices/system/cpu/cpufreq/boost ]]; then
		printf 'boost='; cat /sys/devices/system/cpu/cpufreq/boost
	fi
	printf 'nmi_watchdog='; cat /proc/sys/kernel/nmi_watchdog
	printf 'perf_event_paranoid='; cat /proc/sys/kernel/perf_event_paranoid
	printf 'housekeeping_cpus=%s\n' "$housekeeping_cpus"
	printf 'state_dir=%s\n' "$state_dir"
}

check_benchmark_cpu()
{
	local governor min_freq max_freq boost driver pstate_mode

	governor=$(cat "$cpufreq/scaling_governor")
	min_freq=$(cat "$cpufreq/scaling_min_freq")
	max_freq=$(cat "$cpufreq/scaling_max_freq")
	driver=$(cat "$cpufreq/scaling_driver")
	pstate_mode=not-applicable
	if [[ -f "$amd_pstate_status" ]]; then
		pstate_mode=$(cat "$amd_pstate_status")
	fi
	boost=0
	if [[ -f /sys/devices/system/cpu/cpufreq/boost ]]; then
		boost=$(cat /sys/devices/system/cpu/cpufreq/boost)
	fi

	if [[ "$governor" != "performance" ||
		  "$min_freq" != "$nominal_khz" ||
		  "$max_freq" != "$nominal_khz" ||
		  "$boost" != "0" ||
		  ("$pstate_mode" != "not-applicable" &&
		   ("$pstate_mode" != "$benchmark_pstate_mode" || "$driver" != "amd-pstate")) ]]; then
		echo "benchmark CPU is not in the required stable configuration" >&2
		echo "worker_cpu_id=$cpu driver=$driver amd_pstate_mode=$pstate_mode governor=$governor min_freq=$min_freq max_freq=$max_freq boost=$boost" >&2
		echo "expected driver=amd-pstate amd_pstate_mode=$benchmark_pstate_mode governor=performance min_freq=max_freq=$nominal_khz boost=0" >&2
		return 1
	fi
}

isolate_irqs()
{
	local irq file current
	mkdir -p "$state_dir/irq"
	save_once "$state_dir/default_smp_affinity" "$(cat /proc/irq/default_smp_affinity)"
	printf '%s\n' "$(cpu_list_mask "$housekeeping_cpus")" >/proc/irq/default_smp_affinity

	for file in /proc/irq/[0-9]*/smp_affinity_list; do
		[[ -f "$file" ]] || continue
		irq=${file#/proc/irq/}
		irq=${irq%/smp_affinity_list}
		current=$(cat "$file")
		if cpu_list_contains "$cpu" "$current"; then
			save_once "$state_dir/irq/$irq" "$current"
			if ! printf '%s\n' "$housekeeping_cpus" >"$file" 2>/dev/null; then
				rm -f "$state_dir/irq/$irq"
			fi
		fi
	done
}

isolate_tasks()
{
	local task tid affinity starttime
	touch "$state_dir/task_affinity.tsv"
	for task in /proc/[0-9]*/task/[0-9]*; do
		[[ -r "$task/stat" ]] || continue
		tid=${task##*/}
		affinity=$(taskset -pc "$tid" 2>/dev/null | awk -F': ' 'END {print $2}')
		[[ -n "$affinity" ]] || continue
		if cpu_list_contains "$cpu" "$affinity"; then
			starttime=$(awk '{print $22}' "$task/stat" 2>/dev/null || true)
			[[ -n "$starttime" ]] || continue
			if taskset -pc "$housekeeping_cpus" "$tid" >/dev/null 2>&1; then
				if ! awk -F '\t' -v tid="$tid" -v starttime="$starttime" '
					$1 == tid && $2 == starttime { found = 1 }
					END { exit !found }
				' "$state_dir/task_affinity.tsv"; then
					printf '%s\t%s\t%s\n' "$tid" "$starttime" "$affinity" >>"$state_dir/task_affinity.tsv"
				fi
			fi
		fi
	done
}

restore_tasks()
{
	local tid starttime affinity current
	[[ -f "$state_dir/task_affinity.tsv" ]] || return
	while IFS=$'\t' read -r tid starttime affinity; do
		[[ -r "/proc/$tid/stat" ]] || continue
		current=$(awk '{print $22}' "/proc/$tid/stat")
		[[ "$current" == "$starttime" ]] || continue
		taskset -pc "$affinity" "$tid" >/dev/null 2>&1 || true
	done <"$state_dir/task_affinity.tsv"
}

restore_irqs()
{
	local file irq
	if [[ -f "$state_dir/default_smp_affinity" ]]; then
		cat "$state_dir/default_smp_affinity" >/proc/irq/default_smp_affinity
	fi
	for file in "$state_dir"/irq/*; do
		[[ -f "$file" ]] || continue
		irq=${file##*/}
		cat "$file" >"/proc/irq/$irq/smp_affinity_list" 2>/dev/null || true
	done
}

case "$action" in
	start)
		require_root
		lock_state
		mkdir -p "$state_dir"
	save_once "$state_dir/governor" "$(cat "$state_dir/governor" 2>/dev/null || cat "$cpufreq/scaling_governor")"
	save_once "$state_dir/epp" "$(cat "$state_dir/epp" 2>/dev/null || cat "$cpufreq/energy_performance_preference" 2>/dev/null || true)"
	save_once "$state_dir/nmi_watchdog" "$(cat "$state_dir/nmi_watchdog" 2>/dev/null || cat /proc/sys/kernel/nmi_watchdog)"
	save_once "$state_dir/min_freq" "$(cat "$cpufreq/cpuinfo_min_freq")"
	save_once "$state_dir/max_freq" "$(cat "$cpufreq/scaling_max_freq")"
		[[ ! -f /sys/devices/system/cpu/cpufreq/boost ]] ||
			save_once "$state_dir/boost" "$(cat /sys/devices/system/cpu/cpufreq/boost)"
		[[ ! -f "$amd_pstate_status" ]] ||
			save_once "$state_dir/amd_pstate_status" "$(cat "$amd_pstate_status")"
		save_once "$state_dir/irqbalance_active" "$(systemctl is-active irqbalance 2>/dev/null || true)"

		systemctl stop irqbalance 2>/dev/null || true
		[[ ! -f "$amd_pstate_status" ]] ||
			printf '%s\n' "$benchmark_pstate_mode" >"$amd_pstate_status"
		echo performance >"$cpufreq/scaling_governor"
	[[ ! -f "$cpufreq/energy_performance_preference" ]] ||
		echo performance >"$cpufreq/energy_performance_preference"
	[[ ! -f /sys/devices/system/cpu/cpufreq/boost ]] ||
		echo 0 >/sys/devices/system/cpu/cpufreq/boost
	echo 0 >/proc/sys/kernel/nmi_watchdog
	cat "$cpufreq/cpuinfo_min_freq" >"$cpufreq/scaling_min_freq"
	printf '%s\n' "$nominal_khz" >"$cpufreq/scaling_max_freq"
	printf '%s\n' "$nominal_khz" >"$cpufreq/scaling_min_freq"

	isolate_irqs
	isolate_tasks
	check_benchmark_cpu
	show
	;;
	restore)
		require_root
		lock_state
		restore_tasks
		restore_irqs
		cat "$cpufreq/cpuinfo_min_freq" >"$cpufreq/scaling_min_freq"
		[[ ! -f "$state_dir/amd_pstate_status" ]] ||
			cat "$state_dir/amd_pstate_status" >"$amd_pstate_status"
		cat "$cpufreq/cpuinfo_min_freq" >"$cpufreq/scaling_min_freq"
		[[ ! -f "$state_dir/max_freq" ]] || cat "$state_dir/max_freq" >"$cpufreq/scaling_max_freq"
	[[ ! -f "$state_dir/min_freq" ]] || cat "$state_dir/min_freq" >"$cpufreq/scaling_min_freq"
	[[ ! -f "$state_dir/governor" ]] || cat "$state_dir/governor" >"$cpufreq/scaling_governor"
	[[ ! -f "$state_dir/epp" || ! -f "$cpufreq/energy_performance_preference" ]] ||
		cat "$state_dir/epp" >"$cpufreq/energy_performance_preference"
	[[ ! -f "$state_dir/boost" || ! -f /sys/devices/system/cpu/cpufreq/boost ]] ||
		cat "$state_dir/boost" >/sys/devices/system/cpu/cpufreq/boost
	[[ ! -f "$state_dir/nmi_watchdog" ]] ||
		cat "$state_dir/nmi_watchdog" >/proc/sys/kernel/nmi_watchdog
	if [[ -f "$state_dir/irqbalance_active" ]] &&
		grep -qx active "$state_dir/irqbalance_active"; then
		systemctl start irqbalance 2>/dev/null || true
	fi
	show
	rm -rf "$state_dir"
	;;
status)
	show
	;;
*)
	echo "usage: $0 {start|status|restore} [cpu]" >&2
	exit 1
	;;
esac

#!/usr/bin/env bash
set -euo pipefail

FORMAL_RUNS=5
WARMUP_RUNS=${WARMUP_RUNS:-2}
NROWS=${NROWS:-100000}
EXPECTED_CPU_KHZ=${EXPECTED_CPU_KHZ:-2000000}
REQUIRE_STABLE_CPU=${REQUIRE_STABLE_CPU:-1}
RESTORE_POSTGRES=${RESTORE_POSTGRES:-1}
POSTGRES_STARTED_FOR_BENCHMARK=0

shopt -s expand_aliases
source ~/tool/pg_env.sh

#POSTMASTER_CPU=${POSTMASTER_CPU:-6}
MKSORT_CPU=${MKSORT_CPU:-2}

PSQL=(psql)

restore_postgres_after_benchmark() {
	if [[ "$RESTORE_POSTGRES" != "1" || "$POSTGRES_STARTED_FOR_BENCHMARK" != "1" ]]; then
		return
	fi

	trap - EXIT
	echo "restore postgres: yes"
	"$PGHOME/bin/pg_ctl" -D "$PGDATA" stop -m fast >/dev/null 2>&1 || true
	"$PGHOME/bin/pg_ctl" -D "$PGDATA" -l "$PGDATA/logfile" start >/dev/null
}

trap restore_postgres_after_benchmark EXIT

restart_postgres_for_benchmark() {
	echo "restart postgres: yes"
	echo "autovacuum: off"
	#echo "bind cpu: postmaster $POSTMASTER_CPU"
	echo "bind cpu: backend $MKSORT_CPU"
	"$PGHOME/bin/pg_ctl" -D "$PGDATA" stop -m fast >/dev/null 2>&1 || true
	#taskset -c "$POSTMASTER_CPU" "$PGHOME/bin/pg_ctl" -D "$PGDATA" -l "$PGDATA/logfile" -o "-c autovacuum=off" start >/dev/null
	"$PGHOME/bin/pg_ctl" -D "$PGDATA" -l "$PGDATA/logfile" -o "-c autovacuum=off" start >/dev/null
	POSTGRES_STARTED_FOR_BENCHMARK=1
	sleep 1
	pid=$(pgrep -f "postgres -D $PGDATA" | head -1 || true)
	if [[ -n "${pid:-}" ]]; then
		taskset -pc "$pid"
	fi
}


check_benchmark_cpu() {
	local cpufreq="/sys/devices/system/cpu/cpu$MKSORT_CPU/cpufreq"
	local pstate_status="/sys/devices/system/cpu/amd_pstate/status"
	local governor min_freq max_freq boost driver pstate_mode

	[[ "$REQUIRE_STABLE_CPU" == "1" ]] || return
	governor=$(cat "$cpufreq/scaling_governor")
	min_freq=$(cat "$cpufreq/scaling_min_freq")
	max_freq=$(cat "$cpufreq/scaling_max_freq")
	driver=$(cat "$cpufreq/scaling_driver")
	pstate_mode=not-applicable
	if [[ -f "$pstate_status" ]]; then
		pstate_mode=$(cat "$pstate_status")
	fi
	boost=0
	if [[ -f /sys/devices/system/cpu/cpufreq/boost ]]; then
		boost=$(cat /sys/devices/system/cpu/cpufreq/boost)
	fi

	if [[ "$governor" != "performance" ||
		  "$min_freq" != "$EXPECTED_CPU_KHZ" ||
		  "$max_freq" != "$EXPECTED_CPU_KHZ" ||
		  "$boost" != "0" ||
		  ("$pstate_mode" != "not-applicable" &&
		   ("$pstate_mode" != "passive" || "$driver" != "amd-pstate")) ]]; then
		echo "benchmark CPU is not in the required stable configuration" >&2
		echo "cpu=$MKSORT_CPU driver=$driver amd_pstate_mode=$pstate_mode governor=$governor min_freq=$min_freq max_freq=$max_freq boost=$boost" >&2
		echo "expected driver=amd-pstate amd_pstate_mode=passive governor=performance min_freq=max_freq=$EXPECTED_CPU_KHZ boost=0" >&2
		echo "run: sudo /home/wy/mksort/prepare_benchmark_cpu.sh start $MKSORT_CPU" >&2
		exit 1
	fi

	echo "stable CPU: $MKSORT_CPU"
	echo "CPU driver: $driver ($pstate_mode)"
	echo "CPU frequency: $EXPECTED_CPU_KHZ kHz"
	echo "CPU boost: off"
}
run_sort_query() {
	local mksort=$1
	local timing_file=$2
	local query=$3

	"${PSQL[@]}" test >"$timing_file" <<SQL
SELECT pg_backend_pid() AS backend_pid \gset
\setenv BACKEND_PID :backend_pid
\! taskset -pc $MKSORT_CPU \$BACKEND_PID >/dev/null
SET max_parallel_workers_per_gather = 0 ;
SET work_mem = '1GB';
SET enable_mk_sort = '$mksort';
\o /dev/null
EXPLAIN (ANALYZE, TIMING OFF) $query;
\o
EXPLAIN (ANALYZE, TIMING OFF) $query;
SQL
}

run_case_queries() {
	local query=$1
	local outdir=$2
	local sql_file="$outdir/case.sql"

	rm -rf "$outdir"
	mkdir -p "$outdir"

	{
		echo '\set ON_ERROR_STOP on'
		echo 'SELECT pg_backend_pid() AS backend_pid \gset'
		echo '\setenv BACKEND_PID :backend_pid'
		printf '\\! taskset -pc %s $BACKEND_PID >/dev/null\n' "$MKSORT_CPU"
		echo 'SET max_parallel_workers_per_gather = 0;'
		echo "SET work_mem = '1GB';"

		for r in $(seq 1 "$WARMUP_RUNS"); do
			if ((r % 2)); then
				first=off
				second=on
			else
				first=on
				second=off
			fi
			for mksort in "$first" "$second"; do
				echo "\\o $outdir/warmup-$r-$mksort.log"
				echo "SET enable_mk_sort = '$mksort';"
				echo "EXPLAIN (ANALYZE, TIMING OFF) $query;"
				echo '\o'
			done
		done

		for r in $(seq 1 "$FORMAL_RUNS"); do
			if ((r % 2)); then
				first=off
				second=on
			else
				first=on
				second=off
			fi
			for mksort in "$first" "$second"; do
				echo "\\o $outdir/run-$r-$mksort.log"
				echo "SET enable_mk_sort = '$mksort';"
				echo "EXPLAIN (ANALYZE, TIMING OFF) $query;"
				echo '\o'
			done
		done
	} >"$sql_file"

	"${PSQL[@]}" test -f "$sql_file" >>debug.log 2>&1
}

print_summary() {
	local title=$1
	local input=$2

	echo
	echo "$title"
	python3 - "$input" <<'PY'
from collections import defaultdict
import sys

path = sys.argv[1]
order = ["int", "bigint", "timestamptz", "text", "total"]
vals = defaultdict(list)

try:
    with open(path) as f:
        for line in f:
            parts = line.split()
            if len(parts) != 2:
                continue
            typ, val = parts
            try:
                gain = float(val)
            except ValueError:
                continue
            vals[typ].append(gain)
            vals["total"].append(gain)
except FileNotFoundError:
    pass

print(f"{'type':<12s} {'min':>10s} {'max':>10s} {'avg':>10s} {'n':>6s}")

for typ in order:
    data = sorted(vals.get(typ, []))
    if not data:
        print(f"{typ:<12s} {'n/a':>10s} {'n/a':>10s} {'n/a':>10s} {0:>6d}")
        continue

    avg = sum(data) / len(data)
    print(f"{typ:<12s} {data[0]:+10.2f} {data[-1]:+10.2f} {avg:+10.2f} {len(data):>6d}")
PY
}

print_case_median_summary() {
	local title=$1
	local input=$2

	echo
	echo "$title"
	python3 - "$input" <<'PY'
from collections import defaultdict
import statistics
import sys

path = sys.argv[1]
order = ["int", "bigint", "timestamptz", "text", "total"]
case_vals = defaultdict(list)
vals = defaultdict(list)

try:
    with open(path) as f:
        for line in f:
            parts = line.split()
            if len(parts) != 5:
                continue
            typ, distribution, count, ncols, val = parts
            try:
                gain = float(val)
            except ValueError:
                continue
            case_vals[(typ, distribution, count, ncols)].append(gain)
except FileNotFoundError:
    pass

for key, data in case_vals.items():
    typ = key[0]
    median = statistics.median(data)
    vals[typ].append(median)
    vals["total"].append(median)

print(f"{'type':<12s} {'min_med':>10s} {'max_med':>10s} {'avg_med':>10s} {'median':>10s} {'trim_avg':>10s} {'ncase':>6s}")

for typ in order:
    data = sorted(vals.get(typ, []))
    if not data:
        print(f"{typ:<12s} {'n/a':>10s} {'n/a':>10s} {'n/a':>10s} {'n/a':>10s} {'n/a':>10s} {0:>6d}")
        continue

    avg = sum(data) / len(data)
    median = statistics.median(data)
    if len(data) >= 5:
        trimmed = data[1:-1]
    else:
        trimmed = data
    trim_avg = sum(trimmed) / len(trimmed)

    print(f"{typ:<12s} {data[0]:+10.2f} {data[-1]:+10.2f} {avg:+10.2f} {median:+10.2f} {trim_avg:+10.2f} {len(data):>6d}")
PY
}

print_runtime_outlier_summary() {
	local title=$1
	local input=$2

	echo
	echo "$title"
	python3 - "$input" <<'PY'
from collections import defaultdict
import statistics
import sys

path = sys.argv[1]
order = ["int", "bigint", "timestamptz", "text", "total"]
case_times = defaultdict(list)

try:
    with open(path) as f:
        for line in f:
            parts = line.split()
            if len(parts) != 7:
                continue
            typ, distribution, count, ncols, mksort, mk_enabled, time_ms = parts
            try:
                t = float(time_ms)
            except ValueError:
                continue
            key = (typ, distribution, count, ncols, mksort, mk_enabled)
            case_times[key].append(t)
except FileNotFoundError:
    pass

stats = {typ: {"outliers": 0, "n": 0, "worst_ratio": 1.0, "worst_case": "-"} for typ in order}

for key, times in case_times.items():
    if not times:
        continue
    typ = key[0]
    median = statistics.median(times)
    if median <= 0:
        continue
    for t in times:
        stats[typ]["n"] += 1
        stats["total"]["n"] += 1
        ratio = t / median
        if ratio > stats[typ]["worst_ratio"]:
            stats[typ]["worst_ratio"] = ratio
            stats[typ]["worst_case"] = " ".join(key)
        if ratio > stats["total"]["worst_ratio"]:
            stats["total"]["worst_ratio"] = ratio
            stats["total"]["worst_case"] = " ".join(key)
        # Treat only slow spikes as runtime outliers. With five formal runs
        # per case, median-based detection is more stable than global IQR.
        if ratio >= 1.30:
            stats[typ]["outliers"] += 1
            stats["total"]["outliers"] += 1

print(f"{'type':<12s} {'slow_out':>10s} {'n':>6s} {'max_ratio':>10s} {'worst_case':<48s}")
for typ in order:
    s = stats[typ]
    if s["n"] == 0:
        print(f"{typ:<12s} {0:>10d} {0:>6d} {'n/a':>10s} {'-':<48s}")
    else:
        print(f"{typ:<12s} {s['outliers']:>10d} {s['n']:>6d} {s['worst_ratio']:>10.2f} {s['worst_case']:<48s}")
PY
}

echo "===== nrows type dist reps target_ndistinct actual_ndistinct cols run enable_mk_sort mk_enabled time gain =====";
echo "formal runs per case: $FORMAL_RUNS"
echo "warmup runs per case: $WARMUP_RUNS"
echo "one pinned backend per case; formal samples use balanced AB/BA order"
echo "summary policy: drop one minimum and one maximum gain per case; keep the middle three"

mkdir -p sql
check_benchmark_cpu
restart_postgres_for_benchmark
echo "table row counts: $NROWS"

: > summary.log
: > summary_mk_enabled_yes.log
: > summary_detail.log
: > summary_detail_mk_enabled_yes.log
: > runtime_detail.log
: > debug.log
: > explain-on.log
: > explain-off.log

# number of rows in the table
for nrows in $NROWS; do

	# data type for the columns
	for dtype in int bigint timestamptz text; do

		# number of repetitions for each value (ndistinct = nrows/count)
		unset seen_counts
		declare -A seen_counts=()
		for count in 1 5 10 25 50 100 10000 $((nrows/10)) $nrows; do

			if [[ -n "${seen_counts[$count]:-}" ]]; then
				continue
			fi
			seen_counts[$count]=1

			if [ "$count" -le 0 ] || [ "$count" -gt "$nrows" ]; then
				continue
			fi

			# data distribution for the columns
			for distribution in random correlated sequential; do

				# number of columns
				#for ncols in 1 2 3 4 5 6 7 8; do
				for ncols in 2 5 8; do

					# Generate a table with the specified number of columns
					# and data type. The columns have a given data distribution
					# and number of repetitions of each value.
					#
					# Not executed directly, but writes a SQL script in the
					# "sql" directory to make it easier to reproduce.

					"${PSQL[@]}" test -c "drop table if exists t" >> debug.log 2>&1

					echo "create table t (" > create.sql

					for c in $(seq 1 $ncols); do
						echo "c$c $dtype" >> create.sql
						if [ "$c" != "$ncols" ]; then
							echo ", " >> create.sql
						fi
					done

					echo ");" >> create.sql

					expr=""

					if [ "$distribution" == "random" ]; then
						if [ "$dtype" == "int" ]; then
							expr="(($nrows / $count) * random())"
						elif [ "$dtype" == "bigint" ]; then
							expr="(($nrows / $count) * random())"
						elif [ "$dtype" == "timestamptz" ]; then
							expr="(now() + format('%s days', 1 + (($nrows / $count) * random())::int)::interval)"
						elif [ "$dtype" == "text" ]; then
							expr="((($nrows / $count) * random())::int::text)"
						fi
					elif [ "$distribution" == "correlated" ]; then
						if [ "$dtype" == "int" ]; then
							expr="((i / $count) + random())"
						elif [ "$dtype" == "bigint" ]; then
							expr="((i / $count) + random())"
						elif [ "$dtype" == "timestamptz" ]; then
							expr="(now() + format('%s days', 1 + ((i/$count) + random())::int)::interval)"
						elif [ "$dtype" == "text" ]; then
							expr="(((i / $count) + random())::int::text)"
						fi
					elif [ "$distribution" == "sequential" ]; then
						if [ "$dtype" == "int" ]; then
							expr="((i / $count))"
						elif [ "$dtype" == "bigint" ]; then
							expr="((i / $count))"
						elif [ "$dtype" == "timestamptz" ]; then
							expr="(now() + format('%s days', 1 + ((i/$count)))::interval)"
						elif [ "$dtype" == "text" ]; then
							expr="((i / $count)::int::text)"
						fi
					fi

					echo "insert into t select " >> create.sql

					for c in $(seq 1 $ncols); do
						echo "$expr" >> create.sql
						if [ "$c" != "$ncols" ]; then
							echo ", " >> create.sql
						fi
					done

					echo "from generate_series(1,$nrows) s(i);" >> create.sql

					echo 'vacuum analyze t;' >> create.sql
					echo 'checkpoint;' >> create.sql

					cp create.sql sql/$nrows-$dtype-$count-$distribution-$ncols.sql

					# now actually run the generated SQL script
					"${PSQL[@]}" test < create.sql >> debug.log 2>&1

					ndistinct1=$((nrows/count))
					ndistinct2=$("${PSQL[@]}" -t -A test -c 'select count(distinct c1) from t')

					# generate the ORDER BY query
					query="SELECT * FROM t ORDER BY "

					for c in $(seq 1 $ncols); do
						query="$query $c "
						if [ "$c" != "$ncols" ]; then
							query="$query ,"
						fi
					done

					echo "EXPLAIN (ANALYZE, TIMING OFF) $query" >> explain-on.log;
					echo "EXPLAIN (ANALYZE, TIMING OFF) $query" >> explain-off.log;

					dist_val=$("${PSQL[@]}" test -c "select count(distinct(c1)) from t;" -t);
					dist_ratio=$(awk "BEGIN{print$dist_val/$nrows}");
					echo "distinct: $dist_val (ratio: $dist_ratio)";

					# Warm up both paths for this case. These runs are not
					# summarized because the first executions after data load
					# are more likely to include one-time system noise.
					case_run_dir=$(mktemp -d "/tmp/mksort_case.XXXXXX")
					run_case_queries "$query" "$case_run_dir"

					for r in $(seq 1 "$WARMUP_RUNS"); do
						for mksort in off on; do
							timing_file="$case_run_dir/warmup-$r-$mksort.log"
							echo "===== rows $nrows type $dtype count $count distribution $distribution cols $ncols warmup $r =====" >> explain-$mksort.log 2>&1
							cat "$timing_file" >> explain-$mksort.log 2>&1
						done
					done

					# Keep all five raw runs, then summarize only the middle three.
					case_gain_file="$case_run_dir/formal-gains.tsv"
					effective_gain_file="$case_run_dir/effective-gains.tsv"
					: >"$case_gain_file"
					for r in $(seq 1 "$FORMAL_RUNS"); do

						dif_t="-";
						dif_exact="-";
						for mksort in off on; do

							timing_file="$case_run_dir/run-$r-$mksort.log"
							t=$(grep 'Execution Time' "$timing_file" | awk '{print $3}')
							mk=$(awk '/multi-key/ { found = 1 } END { if (found) print "yes"; else print "no" }' "$timing_file")

							echo "===== rows $nrows type $dtype count $count distribution $distribution cols $ncols run $r =====" >> explain-$mksort.log 2>&1
							cat "$timing_file" >> explain-$mksort.log 2>&1
							echo "$dtype $distribution $count $ncols $mksort $mk $t" >> runtime_detail.log

							if [ "$mksort" == "off" ]; then
								old_t=$t;
							else
								dif_exact=$(awk -v old_t=$old_t -v t=$t 'BEGIN{printf "%+.8f", old_t/t - 1}');
								dif_t=$(awk -v gain=$dif_exact 'BEGIN{printf "%+.2f", gain}');

							fi
							if [ "$mksort" == "on" ]; then
								printf '%s\t%s\t%s\n' "$r" "$mk" "$dif_exact" >>"$case_gain_file"
							fi
							echo $nrows $dtype $distribution $count $ndistinct1 $ndistinct2 $ncols $r $mksort $mk $t $dif_t

						done

					done


					LC_ALL=C sort -t $'\t' -k3,3g "$case_gain_file" |
						sed '1d;$d' >"$effective_gain_file"

					if [[ $(wc -l <"$effective_gain_file") -ne 3 ]]; then
						echo "expected three effective gains for $dtype $distribution count=$count cols=$ncols" >&2
						exit 1
					fi

					echo "effective runs after dropping min/max: $(cut -f1 "$effective_gain_file" | paste -sd, -)"
					while IFS=$'\t' read -r effective_run effective_mk effective_gain; do
						echo "$dtype $effective_gain" >>summary.log
						echo "$dtype $distribution $count $ncols $effective_gain" >>summary_detail.log

						if [[ "$effective_mk" == "yes" ]]; then
							echo "$dtype $effective_gain" >>summary_mk_enabled_yes.log
							echo "$dtype $distribution $count $ncols $effective_gain" >>summary_detail_mk_enabled_yes.log
						fi
					done <"$effective_gain_file"
					rm -rf "$case_run_dir"

				done

			done

		done

	done

done

print_summary "Summary of mksort on relative to off" summary.log
print_summary "Summary of mksort on relative to off (mk_enabled=yes only)" summary_mk_enabled_yes.log
print_runtime_outlier_summary "Summary of per-case runtime slow outliers" runtime_detail.log

# John Naylor's open question: the first key commonly ties, but the second
# key is close to unique. Keep this separate because the main matrix does not
# express this cross-column correlation.
run_john_naylor_candidate() {
	local nrows=${JOHN_NAYLOR_ROWS:-1000000}
	local group_size=${JOHN_NAYLOR_GROUP_SIZE:-10000}
	local min_group_size=1024
	local groups
	local query="SELECT * FROM mksort_john_naylor_candidate ORDER BY c1, c2, c3"
	local outdir
	local results

	if (( nrows <= 0 || group_size < min_group_size || nrows % group_size != 0 )); then
		echo "invalid John Naylor candidate parameters: rows must be divisible by group size, and group size must be >= $min_group_size" >&2
		return 1
	fi

	groups=$((nrows / group_size))
	outdir=$(mktemp -d "/tmp/mksort_john_naylor.XXXXXX")
	results="$outdir/results.tsv"

	echo
	echo "===== John Naylor candidate: tied first key, unique second key ====="
	echo "rows: $nrows, first-key groups: $groups, rows per group: $group_size"
	echo "input order: descending on (c1, c2, c3)"

	"${PSQL[@]}" test <<SQL
DROP TABLE IF EXISTS mksort_john_naylor_candidate;
CREATE UNLOGGED TABLE mksort_john_naylor_candidate (
    c1 int NOT NULL,
    c2 int NOT NULL,
    c3 int NOT NULL
);
INSERT INTO mksort_john_naylor_candidate
SELECT i / $group_size, i % $group_size, i % $group_size
FROM generate_series($((nrows - 1)), 0, -1) AS g(i);
VACUUM ANALYZE mksort_john_naylor_candidate;
CHECKPOINT;
SQL

	# Prove both the intended cardinalities and reverse physical input order.
	"${PSQL[@]}" test -P pager=off <<SQL
SELECT count(*) AS rows,
       count(DISTINCT c1) AS distinct_c1,
       min(group_size) AS min_group_size,
       max(group_size) AS max_group_size,
       min(distinct_c2) AS min_distinct_c2_per_c1,
       max(distinct_c2) AS max_distinct_c2_per_c1
FROM (
    SELECT c1, count(*) AS group_size, count(DISTINCT c2) AS distinct_c2
    FROM mksort_john_naylor_candidate
    GROUP BY c1
) s;
WITH scan AS (
    SELECT c1, c2, c3,
           lag(c1) OVER (ORDER BY ctid) AS previous_c1,
           lag(c2) OVER (ORDER BY ctid) AS previous_c2,
           lag(c3) OVER (ORDER BY ctid) AS previous_c3
    FROM mksort_john_naylor_candidate
)
SELECT count(*) FILTER (WHERE previous_c1 IS NOT NULL) AS adjacent_pairs,
       count(*) FILTER (WHERE previous_c1 IS NOT NULL AND
                         ROW(c1, c2, c3) < ROW(previous_c1, previous_c2, previous_c3)) AS descending_pairs,
       count(*) FILTER (WHERE previous_c1 IS NOT NULL AND
                         ROW(c1, c2, c3) >= ROW(previous_c1, previous_c2, previous_c3)) AS non_descending_pairs
FROM scan;
SQL

	# Each call creates a fresh backend and binds it to MKSORT_CPU.
	for r in $(seq 1 "$WARMUP_RUNS"); do
		for mksort in off on; do
			run_sort_query "$mksort" "$outdir/warmup-$r-$mksort.log" "$query"
		done
	done

	printf "run\tstandard_ms\tmksort_ms\tmksort_method\tgain\n" > "$results"
	for r in $(seq 1 "$FORMAL_RUNS"); do
		local first second standard_file mksort_file standard_ms mksort_ms mksort_method gain
		if (( r % 2 )); then
			first=off
			second=on
		else
			first=on
			second=off
		fi

		for mksort in "$first" "$second"; do
			run_sort_query "$mksort" "$outdir/run-$r-$mksort.log" "$query"
		done

		standard_file="$outdir/run-$r-off.log"
		mksort_file="$outdir/run-$r-on.log"
		standard_ms=$(awk '/Execution Time/ { print $3 }' "$standard_file")
		mksort_ms=$(awk '/Execution Time/ { print $3 }' "$mksort_file")
		mksort_method=$(awk '/multi-key quick sort/ { found = 1 } END { print found ? "multi-key quick sort" : "not used" }' "$mksort_file")
		if [[ "$mksort_method" != "multi-key quick sort" ]]; then
			echo "John Naylor candidate did not enter mksort in run $r" >&2
			return 1
		fi
		gain=$(awk -v standard_ms="$standard_ms" -v mksort_ms="$mksort_ms" \
			'BEGIN { printf "%+.4f", standard_ms / mksort_ms - 1 }')
		printf "%s\t%s\t%s\t%s\t%s\n" "$r" "$standard_ms" "$mksort_ms" "$mksort_method" "$gain" | tee -a "$results"
	done

	python3 - "$results" <<'PY'
import statistics
import sys

rows = []
with open(sys.argv[1]) as f:
    next(f)
    for line in f:
        run, standard, mksort, method, gain = line.rstrip().split("\t")
        rows.append((float(standard), float(mksort), float(gain)))

standard = [row[0] for row in rows]
mksort = [row[1] for row in rows]
gains = [row[2] for row in rows]
print()
print(f"formal runs: {len(rows)} (one fresh backend per path per run)")
print(f"standard ms: min={min(standard):.3f} median={statistics.median(standard):.3f} max={max(standard):.3f}")
print(f"mksort   ms: min={min(mksort):.3f} median={statistics.median(mksort):.3f} max={max(mksort):.3f}")
print(f"gain (standard/mksort - 1): min={min(gains):+.4f} median={statistics.median(gains):+.4f} max={max(gains):+.4f}")
PY

	echo "John Naylor candidate logs: $outdir"
}

run_john_naylor_candidate

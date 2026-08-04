#!/usr/bin/env bash
set -euo pipefail

# Focused hardware experiment for John Naylor's review comment.  The script
# measures the largest stable benefit case from new_result_3.txt:
#   100000 rows, text, correlated, reps=10000, 8 sort keys.
#
# PHASE=all     Run software counters and perf (default).
# PHASE=profile Run only the temporary comparison/swap instrumentation.
# PHASE=perf    Run only perf on the currently installed clean release build.

PHASE=${PHASE:-all}
FORMAL_RUNS=${FORMAL_RUNS:-5}
WARMUP_RUNS=${WARMUP_RUNS:-2}
MKSORT_CPU=${MKSORT_CPU:-2}
REPO=${REPO:-/home/wy/postgres}
OUTROOT=${OUTROOT:-/home/wy/mksort/john-hardware-artifacts}
PATCH_FILE=
PROFILE_APPLIED=0
BENCHMARK_SERVER=0
NEED_NORMAL_BUILD=0
ORIGINAL_PERF_PARANOID=

shopt -s expand_aliases
source /home/wy/tool/pg_env.sh

mkdir -p "$OUTROOT"
if [[ "$PHASE" == all || "$PHASE" == profile ]]; then
	rm -rf "$OUTROOT/profile"
	mkdir -p "$OUTROOT/profile"
fi
if [[ "$PHASE" == all || "$PHASE" == perf ]]; then
	rm -rf "$OUTROOT/perf"
	mkdir -p "$OUTROOT/perf"
fi

stop_server() {
	"$PGHOME/bin/pg_ctl" -D "$PGDATA" stop -m fast >/dev/null 2>&1 || true
}

start_benchmark_server() {
	stop_server
	"$PGHOME/bin/pg_ctl" -D "$PGDATA" -l "$PGDATA/logfile" \
		-o '-c autovacuum=off' start >/dev/null
	BENCHMARK_SERVER=1
}

start_normal_server() {
	stop_server
	"$PGHOME/bin/pg_ctl" -D "$PGDATA" -l "$PGDATA/logfile" start >/dev/null
	BENCHMARK_SERVER=0
}

full_release_build() {
	(
		cd "$REPO"
		source /home/wy/tool/pg_env.sh
		/home/wy/tool/pg_fullbld_rel.sh
	)
}

restore_sources() {
	if ((PROFILE_APPLIED)); then
		(cd "$REPO" && git apply -R "$PATCH_FILE")
		PROFILE_APPLIED=0
		NEED_NORMAL_BUILD=1
	fi
}

cleanup() {
	local status=$?
	trap - EXIT INT TERM

	restore_sources || status=$?
	if ((NEED_NORMAL_BUILD)); then
		full_release_build >/dev/null 2>&1 || status=$?
		NEED_NORMAL_BUILD=0
	fi
	if ((BENCHMARK_SERVER)); then
		start_normal_server || status=$?
	fi
	if [[ -n "$ORIGINAL_PERF_PARANOID" ]]; then
		sudo sysctl -q -w "kernel.perf_event_paranoid=$ORIGINAL_PERF_PARANOID" || status=$?
	fi
	if [[ -n "$PATCH_FILE" ]]; then
		rm -f "$PATCH_FILE"
	fi
	exit "$status"
}
trap cleanup EXIT INT TERM

case "$PHASE" in
	all|profile|perf) ;;
	*) echo "invalid PHASE: $PHASE" >&2; exit 1 ;;
esac

cd "$REPO"
for file in \
	src/backend/utils/sort/tuplesort.c \
	src/backend/utils/sort/tuplesortvariants.c \
	src/backend/utils/sort/mk_qsort_tuple.c \
	src/backend/utils/sort/mk_qsort_tuple_template.h \
	src/include/lib/sort_template.h
do
	if ! git diff --quiet -- "$file"; then
		echo "refusing to overwrite existing change: $file" >&2
		exit 1
	fi
done

sudo /home/wy/mksort/prepare_benchmark_cpu.sh start "$MKSORT_CPU" \
	>"$OUTROOT/cpu.txt"

create_data() {
	"$PGHOME/bin/psql" -X -v ON_ERROR_STOP=1 test >"$OUTROOT/data.log" <<'SQL'
DROP TABLE IF EXISTS mkqs_john_hw;
SELECT setseed(0.20260804);
CREATE UNLOGGED TABLE mkqs_john_hw
  (c1 text, c2 text, c3 text, c4 text,
   c5 text, c6 text, c7 text, c8 text);
INSERT INTO mkqs_john_hw
SELECT (((i / 10000) + random())::int::text),
       (((i / 10000) + random())::int::text),
       (((i / 10000) + random())::int::text),
       (((i / 10000) + random())::int::text),
       (((i / 10000) + random())::int::text),
       (((i / 10000) + random())::int::text),
       (((i / 10000) + random())::int::text),
       (((i / 10000) + random())::int::text)
FROM generate_series(1, 100000) AS g(i);
VACUUM ANALYZE mkqs_john_hw;
CHECKPOINT;
SELECT count(*) AS rows,
       count(DISTINCT c1) AS distinct_c1,
       count(DISTINCT (c1,c2,c3,c4,c5,c6,c7,c8)) AS distinct_rows
FROM mkqs_john_hw;
SQL
}

write_profile_patch() {
	PATCH_FILE=$(mktemp /tmp/mkqs-john-profile.XXXXXX.patch)
	cat >"$PATCH_FILE" <<'PATCH'
diff --git a/src/backend/utils/sort/mk_qsort_tuple.c b/src/backend/utils/sort/mk_qsort_tuple.c
--- a/src/backend/utils/sort/mk_qsort_tuple.c
+++ b/src/backend/utils/sort/mk_qsort_tuple.c
@@ -54,6 +54,7 @@ mkqs_swap(int a,
 
 	if (a == b)
 		return;
+	mkqs_john_swaps++;
 	t = x[a];
 	x[a] = x[b];
 	x[b] = t;
@@ -117,6 +118,7 @@ mkqs_compare_abbrev_full_datum(Datum datum1, Datum datum2,
 {
 	int			compare;
 
+	mkqs_john_comparisons++;
 	compare = sortKey->abbrev_full_comparator(datum1, datum2, sortKey);
 	if (sortKey->ssup_reverse)
 		INVERT_COMPARE_RESULT(compare);
diff --git a/src/backend/utils/sort/mk_qsort_tuple_template.h b/src/backend/utils/sort/mk_qsort_tuple_template.h
--- a/src/backend/utils/sort/mk_qsort_tuple_template.h
+++ b/src/backend/utils/sort/mk_qsort_tuple_template.h
@@ -53,6 +53,7 @@ MKQS_APPLY_COMPARE(Datum datum1, bool isNull1,
 {
 	int			compare;
 
+	mkqs_john_comparisons++;
 	if (isNull1 || isNull2)
 	{
 		if (isNull1 && isNull2)
diff --git a/src/backend/utils/sort/tuplesort.c b/src/backend/utils/sort/tuplesort.c
--- a/src/backend/utils/sort/tuplesort.c
+++ b/src/backend/utils/sort/tuplesort.c
@@ -129,6 +129,12 @@ bool		optimize_bounded_sort = true;
 
 bool		enable_mk_sort = true;
 
+/* Temporary counters used by mksort_john_hardware_test.sh. */
+extern uint64 mkqs_john_comparisons;
+extern uint64 mkqs_john_swaps;
+uint64		mkqs_john_comparisons = 0;
+uint64		mkqs_john_swaps = 0;
+
 /*
  * During merge, we use a pre-allocated set of fixed-size slots to hold
  * tuples.  To avoid palloc/pfree overhead.
@@ -494,6 +500,8 @@ static void tuplesort_updatemax(Tuplesortstate *state);
 #define ST_SORT qsort_tuple
 #define ST_ELEMENT_TYPE SortTuple
 #define ST_COMPARE_RUNTIME_POINTER
+#define ST_SWAP_CALLBACK(a, b) \
+	do { if ((a) != (b)) mkqs_john_swaps++; } while (0)
 #define ST_COMPARE_ARG_TYPE Tuplesortstate
 #define ST_CHECK_FOR_INTERRUPTS
 #define ST_SCOPE static
@@ -3068,6 +3076,8 @@ static void
 tuplesort_sort_memtuples(Tuplesortstate *state)
 {
 	Assert(!LEADER(state));
+	mkqs_john_comparisons = 0;
+	mkqs_john_swaps = 0;
 
 	if (state->memtupcount > 1)
 	{
@@ -3127,6 +3137,9 @@ tuplesort_sort_memtuples(Tuplesortstate *state)
 							   false);
 			}
 			verify_memtuples_sorted(state);
+			ereport(NOTICE,
+					(errmsg("MKQS_JOHN_PROFILE method=mksort comparisons=%" PRIu64 " swaps=%" PRIu64,
+							mkqs_john_comparisons, mkqs_john_swaps)));
 
 			return;
 		}
@@ -3167,6 +3180,9 @@ tuplesort_sort_memtuples(Tuplesortstate *state)
 						state->base.comparetup,
 						state);
 		}
+		ereport(NOTICE,
+				(errmsg("MKQS_JOHN_PROFILE method=standard comparisons=%" PRIu64 " swaps=%" PRIu64,
+						mkqs_john_comparisons, mkqs_john_swaps)));
 	}
 }
 
diff --git a/src/backend/utils/sort/tuplesortvariants.c b/src/backend/utils/sort/tuplesortvariants.c
--- a/src/backend/utils/sort/tuplesortvariants.c
+++ b/src/backend/utils/sort/tuplesortvariants.c
@@ -45,6 +45,8 @@
 #define DATUM_SORT		2
 #define CLUSTER_SORT	3
 
+extern uint64 mkqs_john_comparisons;
+
 static void removeabbrev_heap(Tuplesortstate *state, SortTuple *stups,
 							  int count);
 static void removeabbrev_cluster(Tuplesortstate *state, SortTuple *stups,
@@ -1257,6 +1259,7 @@ comparetup_heap(const SortTuple *a, const SortTuple *b, Tuplesortstate *state)
 
 
 	/* Compare the leading sort key */
+	mkqs_john_comparisons++;
 	compare = ApplySortComparator(a->datum1, a->isnull1,
 								  b->datum1, b->isnull1,
 								  sortKey);
@@ -1296,6 +1299,7 @@ comparetup_heap_tiebreak(const SortTuple *a, const SortTuple *b, Tuplesortstate
 		datum1 = heap_getattr(&ltup, attno, tupDesc, &isnull1);
 		datum2 = heap_getattr(&rtup, attno, tupDesc, &isnull2);
 
+		mkqs_john_comparisons++;
 		compare = ApplySortAbbrevFullComparator(datum1, isnull1,
 												datum2, isnull2,
 												sortKey);
@@ -1311,6 +1315,7 @@ comparetup_heap_tiebreak(const SortTuple *a, const SortTuple *b, Tuplesortstate
 		datum1 = heap_getattr(&ltup, attno, tupDesc, &isnull1);
 		datum2 = heap_getattr(&rtup, attno, tupDesc, &isnull2);
 
+		mkqs_john_comparisons++;
 		compare = ApplySortComparator(datum1, isnull1,
 									  datum2, isnull2,
 									  sortKey);
diff --git a/src/include/lib/sort_template.h b/src/include/lib/sort_template.h
--- a/src/include/lib/sort_template.h
+++ b/src/include/lib/sort_template.h
@@ -274,6 +274,9 @@ ST_SWAP(ST_POINTER_TYPE * a, ST_POINTER_TYPE * b)
 {
 	ST_POINTER_TYPE tmp = *a;
 
+#ifdef ST_SWAP_CALLBACK
+	ST_SWAP_CALLBACK(a, b);
+#endif
 	*a = *b;
 	*b = tmp;
 }
@@ -443,5 +446,6 @@ loop:
 #undef ST_SORT_PROTO_ARG
 #undef ST_SORT_PROTO_COMPARE
 #undef ST_SORT_PROTO_ELEMENT_SIZE
+#undef ST_SWAP_CALLBACK
 #undef ST_SWAP
 #undef ST_SWAPN
PATCH
}

run_profile() {
	write_profile_patch
	git apply "$PATCH_FILE"
	PROFILE_APPLIED=1
	NEED_NORMAL_BUILD=1
	full_release_build >"$OUTROOT/profile/build.log" 2>&1
	start_benchmark_server
	create_data

	for mode in off on; do
		"$PGHOME/bin/psql" -X -v ON_ERROR_STOP=1 test \
			>"$OUTROOT/profile/$mode.log" 2>&1 <<SQL
SELECT pg_backend_pid() AS backend_pid \gset
\setenv BACKEND_PID :backend_pid
\! taskset -pc $MKSORT_CPU \$BACKEND_PID >/dev/null
SET work_mem='1GB';
SET max_parallel_workers_per_gather=0;
SET enable_mk_sort=$mode;
EXPLAIN (ANALYZE, TIMING OFF)
SELECT * FROM mkqs_john_hw ORDER BY 1,2,3,4,5,6,7,8;
SQL
	done
	rg 'MKQS_JOHN_PROFILE|Sort Method|Execution Time' "$OUTROOT/profile"/*.log \
		>"$OUTROOT/profile/summary.txt"

	restore_sources
	full_release_build >"$OUTROOT/profile/restore-build.log" 2>&1
	NEED_NORMAL_BUILD=0
	start_benchmark_server
}

append_perf_measurement() {
	local sql_file=$1
	local run=$2
	local mode=$3
	local base="$OUTROOT/perf/run-$run-$mode"
	local ctl="$base.ctl"
	local ack="$base.ack"
	local pidfile="$base.pid"

	cat >>"$sql_file" <<SQL
SET enable_mk_sort=$mode;
\o $base.plan
\! rm -f $ctl $ack $pidfile $base.csv $base.nohup
\! mkfifo $ctl $ack
\! nohup perf stat -D -1 -x, -e cycles,instructions,branches,branch-misses,cache-misses -p \$BACKEND_PID --control fifo:$ctl,$ack -o $base.csv >$base.nohup 2>&1 & echo \$! >$pidfile
\! printf 'enable\\n' >$ctl; read response <$ack
EXPLAIN (ANALYZE, TIMING OFF)
SELECT * FROM mkqs_john_hw ORDER BY 1,2,3,4,5,6,7,8;
\! printf 'disable\\n' >$ctl; read response <$ack
\! kill -INT \`cat $pidfile\`; sleep 0.2
\o
SQL
}

run_perf() {
	local sql_file="$OUTROOT/perf/run.sql"

	if ((PROFILE_APPLIED)); then
		echo 'internal error: perf cannot run with profile instrumentation' >&2
		exit 1
	fi
	start_benchmark_server
	create_data
	ORIGINAL_PERF_PARANOID=$(cat /proc/sys/kernel/perf_event_paranoid)
	sudo sysctl -q -w kernel.perf_event_paranoid=-1

	cat >"$sql_file" <<SQL
\set ON_ERROR_STOP on
SELECT pg_backend_pid() AS backend_pid \gset
\setenv BACKEND_PID :backend_pid
\! taskset -pc $MKSORT_CPU \$BACKEND_PID >/dev/null
SET work_mem='1GB';
SET max_parallel_workers_per_gather=0;
SQL

	for run in $(seq 1 "$WARMUP_RUNS"); do
		if ((run % 2)); then modes='off on'; else modes='on off'; fi
		for mode in $modes; do
			cat >>"$sql_file" <<SQL
SET enable_mk_sort=$mode;
\o /dev/null
EXPLAIN (ANALYZE, TIMING OFF)
SELECT * FROM mkqs_john_hw ORDER BY 1,2,3,4,5,6,7,8;
\o
SQL
		done
	done

	for run in $(seq 1 "$FORMAL_RUNS"); do
		if ((run % 2)); then modes='off on'; else modes='on off'; fi
		for mode in $modes; do
			append_perf_measurement "$sql_file" "$run" "$mode"
		done
	done

	"$PGHOME/bin/psql" -X test -f "$sql_file" >"$OUTROOT/perf/psql.log" 2>&1

	python3 - "$OUTROOT/perf" "$FORMAL_RUNS" >"$OUTROOT/perf/summary.txt" <<'PY'
import statistics
import sys
from pathlib import Path

root = Path(sys.argv[1])
runs = int(sys.argv[2])
events = ["cycles", "instructions", "branches", "branch-misses", "cache-misses"]

def read_plan(run, mode):
    text = (root / f"run-{run}-{mode}.plan").read_text()
    method = None
    elapsed = None
    for line in text.splitlines():
        if "Sort Method:" in line:
            method = line.split("Sort Method:", 1)[1].split("Memory:", 1)[0].strip()
        if "Execution Time:" in line:
            elapsed = float(line.split()[2])
    if method is None or elapsed is None:
        raise RuntimeError(f"incomplete plan for run {run} {mode}")
    return method, elapsed

def read_perf(run, mode):
    values = {}
    for line in (root / f"run-{run}-{mode}.csv").read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split(",")
        if len(parts) >= 3 and parts[2] in events:
            values[parts[2]] = int(parts[0])
    missing = set(events) - set(values)
    if missing:
        raise RuntimeError(f"missing perf events for run {run} {mode}: {sorted(missing)}")
    return values

rows = []
print("run off_ms on_ms gain off_method on_method")
for run in range(1, runs + 1):
    off_method, off_ms = read_plan(run, "off")
    on_method, on_ms = read_plan(run, "on")
    if off_method != "quicksort" or on_method != "multi-key quick sort":
        raise RuntimeError(f"unexpected methods: {off_method!r}, {on_method!r}")
    off = read_perf(run, "off")
    on = read_perf(run, "on")
    rows.append((off_ms, on_ms, off, on))
    print(run, f"{off_ms:.3f}", f"{on_ms:.3f}", f"{off_ms/on_ms-1:+.5f}",
          off_method, on_method)

print()
print(f"runtime median off/on: {statistics.median(r[0] for r in rows):.3f} "
      f"{statistics.median(r[1] for r in rows):.3f} ms")
print(f"gain median: {statistics.median(r[0]/r[1]-1 for r in rows):+.5f}")
print()
print("event off_median on_median reduction(1-on/off)")
for event in events:
    off = statistics.median(r[2][event] for r in rows)
    on = statistics.median(r[3][event] for r in rows)
    print(f"{event} {off:.0f} {on:.0f} {1-on/off:+.5f}")

off_cycles = statistics.median(r[2]["cycles"] for r in rows)
on_cycles = statistics.median(r[3]["cycles"] for r in rows)
off_insn = statistics.median(r[2]["instructions"] for r in rows)
on_insn = statistics.median(r[3]["instructions"] for r in rows)
off_br = statistics.median(r[2]["branches"] for r in rows)
on_br = statistics.median(r[3]["branches"] for r in rows)
off_brm = statistics.median(r[2]["branch-misses"] for r in rows)
on_brm = statistics.median(r[3]["branch-misses"] for r in rows)
print()
print(f"IPC off/on: {off_insn/off_cycles:.4f} {on_insn/on_cycles:.4f}")
print(f"branch miss rate off/on: {off_brm/off_br:.6%} {on_brm/on_br:.6%}")
PY
}

if [[ "$PHASE" == all || "$PHASE" == profile ]]; then
	run_profile
fi
if [[ "$PHASE" == all || "$PHASE" == perf ]]; then
	run_perf
fi

if [[ -n "$ORIGINAL_PERF_PARANOID" ]]; then
	sudo sysctl -q -w "kernel.perf_event_paranoid=$ORIGINAL_PERF_PARANOID"
	ORIGINAL_PERF_PARANOID=
fi
start_normal_server

echo "results: $OUTROOT"
if [[ -f "$OUTROOT/profile/summary.txt" ]]; then
	cat "$OUTROOT/profile/summary.txt"
fi
if [[ -f "$OUTROOT/perf/summary.txt" ]]; then
	cat "$OUTROOT/perf/summary.txt"
fi

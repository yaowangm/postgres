# mksort Performance Regression Analysis and Next-Step Plan

## Background

The mksort patch introduces multi-key quicksort for PostgreSQL tuple sorting.
The expected benefit is strongest when earlier sort keys contain many duplicate
values, because mksort can partition on one key at a time and postpone later-key
comparisons until they are needed.

The current concern is that benchmark reports show regressions up to about 5%.
More concerning, similar regressions have reportedly appeared even when the
classic sort path is used. John Naylor's latest email in
`/home/wy/download/mksort.html` challenges both the interpretation of those
numbers and the current implementation structure.

This document summarizes the problem, John Naylor's feedback, likely causes,
and a concrete plan for producing credible performance evidence and improving
the patch.

## Key Points From John Naylor's Feedback

### 1. A 5% regression is not normal noise

John's position is that most observed variation appears to be around 1%, and he
is willing to treat that as noise. He explicitly says that if regressions are
commonly 5%, that is a cause for concern. If the actual benchmark noise is 5%,
then the test methodology is not strict enough.

Implication:

The report should not claim that "less than 5%" is simply an error range unless
an A/A test proves that the same binary under the same workload naturally varies
by that much. If A/A noise is really near 5%, the benchmark cannot support
claims about 1% regressions or improvements.

### 2. Current tests do not prove a worst-case bound

John agrees with the concerns about using `stadistinct` and planner estimates.
He points out that the current tests use ideal, well-behaved data without
filters. That does not establish that the worst regression is only 5%.

The real worst case is likely when estimates are wrong. In realistic workloads,
filters, correlations, expression sort keys, stale statistics, and multi-column
dependencies can make table-level `stadistinct` misleading. Under those
conditions, planner-based selection could enable mksort when it should not, and
regressions could plausibly return to 10-20%, which John considers
unacceptable.

Implication:

The optimizer-selection patch cannot be justified only by ideal synthetic
datasets. It needs adversarial cases where the statistics are incomplete or
wrong.

### 3. The cause of performance differences is not yet understood

John asks for a hardware-level explanation for the largest benefit and
regression cases:

- number of comparisons
- number of swaps
- cache misses
- branch mispredicts

Implication:

The benchmark report should not only show elapsed time. It should explain why a
case is faster or slower. Without that, it is hard to distinguish algorithmic
benefit from measurement noise, code layout effects, or branch/cache behavior.

### 4. Several sanity-check cases are missing

John suggests cases that should be tested:

- first key is unique
- first key commonly ties and later keys also tie
- first key commonly ties but the second key is close to unique
- only one sort key, where a single-depth multi-key sort should ideally behave
  like standard sort

Implication:

The current test matrix is not sufficient. It needs cases designed to isolate
the algorithmic tradeoff.

### 5. The implementation spreads btree TID tiebreak knowledge too widely

In standard sort, btree TID tiebreak behavior is confined to btree's full
`comparetup` function. In the mksort patch, generic mksort code has to know
about duplicate tuples and pass `seenNull` down to duplicate handling.

John suggests a design where a multi-key compare function accepts
`start_depth` and `max_depth`. A btree implementation could interpret a depth
beyond the last explicit sort key as the signal to compare TIDs. That would
avoid a separate generic duplicate-handling abstraction and might remove the
need for a separate `getDatum` function.

Implication:

The current abstraction is probably too generic in the wrong place. It leaks
btree-specific behavior into generic mksort control flow.

### 6. Pre-ordered checks are semantically unclear

John does not understand why the pre-ordered check sometimes tolerates
duplicates and sometimes does not.

Current code has different behavior depending on comparator mode:

- specialized comparator path checks whether the whole tuple order is
  non-decreasing
- generic path requires strict ordering at the current depth because equal keys
  must still be sorted at deeper depths

Implication:

Even if the behavior is technically defensible, it is hard to review and easy
to get wrong. The design should express the rule in terms of depth and
remaining sort keys, rather than as a special case of comparator type.

### 7. "Tiebreak" terminology does not fit mksort well

John says standard sort's tiebreak paths are already somewhat awkward, and that
the terminology is more out of place in mksort. mksort naturally has a concept
of depth, so the implementation should use depth consistently.

Implication:

The design should move from "shortcut vs tiebreak" toward a general
"compare range of depths" model.

### 8. Shortcut and abbreviated comparisons could be modeled as earlier depths

John raises the idea that shortcut or abbreviated comparisons might be treated
as their own depth less than zero. If postponing later keys is beneficial, it
might also be beneficial to postpone the full comparison for the first key.

Implication:

This is exploratory, not a required change. But it reinforces the need for a
clean depth model that can represent abbreviated keys, full first-key
comparison, and later-key comparison uniformly.

### 9. NULL handling may deserve separation

John notes that separating all NULL first keys into a separate array could
remove NULL-ordering branches and potentially reduce `SortTuple` size.

Implication:

This is future work, not required for the current patch. But it points to the
same architectural direction: separate cases before entering the hot loop, do
not keep checking every possibility inside the comparator.

### 10. The hot path is too branch-heavy

John says stuffing all optimized comparators into the same path is heroic but
messy, and seems bad for instruction cache and branch predictor behavior. He
does not think another template is necessarily required, but recommends taking
some branches as recursion enters a partition so they are kept out of the hot
path.

Implication:

The main optimization direction should be path specialization by state already
known at recursion time. This is more targeted than simply converting
everything to a macro template.

### 11. Small-array threshold comparison is not controlled

The patch uses a threshold of 16 for small-array insertion/bubble sort, while
standard qsort uses 7. John points out that 7 is not necessarily ideal either,
and if one implementation has a better-tuned threshold than the other, it
obscures the true tradeoff. He also notes the implementation appears to be
insertion sort, not bubble sort.

Implication:

Thresholds should be tested systematically and named accurately. Comparing
mksort with threshold 16 to qsort with threshold 7 may not isolate the
algorithmic difference.

## Current Code Observations

### Classic path

In `src/backend/utils/sort/tuplesort.c`, mksort is selected only when all of the
following are true:

- `enable_mk_sort`
- more than one sort key
- `mkqsGetDatumFunc` is available
- `state->mkqsApplicable`

If those conditions are false, the code proceeds to radix sort or qsort. That
means a large regression in classic sort is unlikely to be caused by the mksort
algorithm itself. It could still be caused by:

- benchmark noise
- code layout or instruction-cache effects
- the extra dispatch branch
- planner changes that alter the actual plan or sort input
- build differences
- runtime environment differences

### mksort comparator path

The mksort comparison code currently handles several concerns in one path:

- depth zero shortcut comparison
- abbreviated key full comparison
- per-depth datum extraction through `mkqsGetDatumFunc`
- NULL handling
- range comparison across remaining keys
- btree duplicate handling through `mkqsHandleDupFunc`

This makes the hot comparator path hard for the compiler and branch predictor.
It also makes the performance model harder to explain.

### mksort recursion path

The main recursive function handles:

- pre-ordered checks
- small-array insertion sort
- pivot selection
- partitioning into less/equal/greater groups
- recursion at the same depth for less/greater groups
- recursion at the next depth for equal groups
- final duplicate handling at maximum depth

This is conceptually valid for multi-key quicksort, but the implementation
mixes algorithmic control flow with tuple-kind-specific handling. That is the
source of several review concerns.

## Likely Causes of the Observed Regressions

### Most likely cause for classic sort regression: benchmark instability

If classic sort shows up to 5% regression even when mksort is disabled or not
selected, the most likely explanation is benchmark instability. Possible
sources include:

- VM scheduling noise
- non-dedicated test machine load
- CPU frequency scaling
- thermal throttling
- background services
- cache state differences
- running all tests for one version before the other
- insufficient repetitions
- reporting maximum values instead of median and dispersion
- different binaries or build options

This is especially likely because John says he mostly sees about 1% variation,
not 5%.

### Possible cause for classic path regression: code layout or dispatch effects

If bare-metal A/A tests are stable but `enable_mk_sort=off` still regresses,
then the remaining possibilities include:

- added branch in `tuplesort_sort_memtuples`
- changed function size and instruction-cache layout
- changed compiler optimization decisions because `mk_qsort_tuple.c` is
  included in `tuplesort.c`
- changed planner or instrumentation fields
- changed generated plan due to optimizer additions

This should be tested separately by building a patch variant that removes the
mksort dispatch while keeping unrelated changes, and another variant that keeps
only the dispatch.

### Most likely cause for mksort-specific regression: hot-path complexity

For cases where mksort itself is slower, likely causes are:

- branch mispredicts from handling many comparator modes in one path
- instruction-cache pressure from large inlined logic
- repeated datum extraction through function pointers
- extra work from pre-ordered checks
- small-array threshold differences
- later-key comparisons not being avoided enough for certain data
  distributions
- bad heuristic selection from `stadistinct`

The specific cause should be established with perf counters and internal
instrumentation.

### Planner-statistics risk

`stadistinct` is an incomplete signal for mksort applicability. It can be
wrong or unavailable for:

- expression sort keys
- computed sort keys without a base table column
- filtered result sets
- stale statistics
- correlated columns
- multi-column distributions
- joins
- parameterized queries

Therefore planner selection should be conservative. It should not be presented
as proving a worst-case regression bound.

## Test Machine Plan

Target machine:

- CPU: AMD AI 9 HX 370
- Memory: 64 GB
- Storage: 1 TB SSD
- OS: Ubuntu 26.04

This machine is suitable for the next round of testing, provided it is
configured for stable measurements.

### System preparation

Install required tools:

```bash
sudo apt install build-essential meson ninja-build flex bison \
  libreadline-dev zlib1g-dev libssl-dev libicu-dev pkg-config \
  linux-tools-common linux-tools-generic numactl
```

Reduce background noise:

```bash
sudo systemctl stop unattended-upgrades || true
sudo systemctl stop packagekit || true
```

Set CPU governor:

```bash
sudo cpupower frequency-set -g performance
cat /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor | sort | uniq -c
```

Use CPU affinity for PostgreSQL and client commands:

```bash
taskset -c 4 psql -p 5500 -d postgres -f bench.sql
```

If results remain noisy, test with SMT disabled in BIOS or by restricting tests
to isolated physical cores.

### Build discipline

Use identical build options across all variants.

Recommended variants:

1. `master`: unmodified upstream baseline.
2. `mksort-off`: patch applied, but `enable_mk_sort=off`.
3. `mksort-on`: patch applied, `enable_mk_sort=on`.
4. `dispatch-removed`: patch variant with mksort dispatch removed, to isolate
   classic path effects.
5. `optimizer-off`: mksort patch without planner selection.
6. `optimizer-on`: mksort patch with `mkqsApplicable` planner selection.

Do not compare binaries built with different compilers, flags, configure
options, or assertion settings.

## Benchmark Methodology

### Phase 1: A/A noise measurement

Before comparing versions, test the same binary against itself.

For each representative query:

- run the same SQL 30-50 times
- keep the same PostgreSQL instance
- keep the same dataset
- run with CPU affinity
- report median, MAD, standard deviation, min, and max

Acceptance criterion:

If A/A variation is near 5%, the environment or script is not strict enough.
Do not use that setup to make claims about 1% regressions.

### Phase 2: A/B/C comparison

Compare variants in interleaved order:

```text
master
mksort-off
mksort-on
master
mksort-off
mksort-on
...
```

Avoid running all iterations of one variant before the next variant. That can
confound results with temperature, cache state, and background activity.

For each variant and case, collect:

- elapsed time
- median
- MAD or standard deviation
- min and max
- whether mksort was enabled by planner
- actual sort method from `EXPLAIN ANALYZE`

### Phase 3: hardware-counter analysis

For the largest benefit and largest regression cases, collect:

```bash
taskset -c 4 perf stat -r 30 \
  -e cycles,instructions,branches,branch-misses,cache-misses \
  psql -p 5500 -d postgres -f bench.sql
```

Interpretation:

- higher instructions suggests extra work
- higher cycles with similar instructions suggests stalls, cache, branch, or
  frequency effects
- higher branch-misses supports John's branch predictor concern
- higher cache-misses supports instruction/data-cache concern

### Phase 4: internal instrumentation

Add temporary counters for mksort-only profiling:

- datum comparisons
- full tuple/range comparisons
- swaps
- calls to `mkqsGetDatumFunc`
- calls to duplicate handling
- recursion depth
- number and size of equal partitions
- number of pre-ordered check comparisons

These counters should be compiled only for benchmarking and not proposed as
final patch content.

## Required Test Matrix

### Sanity cases

1. Single sort key.
   Expected: mksort with single depth should have no significant difference
   from standard sort, or should not be selected.

2. First key unique.
   Expected: mksort should be close to standard sort. Large regression means
   the mksort overhead is too high.

3. First key ties, later keys also tie.
   Expected: mksort may win because later comparisons can be postponed and
   partitioning one key at a time can avoid waste.

4. First key ties, second key near unique.
   Expected: uncertain. This is one of John's requested cases and may define
   the actual tradeoff boundary.

### Data layout cases

For each key distribution, test:

- random layout
- correlated layout
- sequential or pre-ordered layout

This matters because current results already show that the same distinct ratio
can produce different outcomes depending on data layout.

### Statistics-risk cases

Test cases where planner estimates are likely wrong:

- `WHERE` filter that changes distinct ratio after filtering
- stale statistics after data updates
- expression sort key
- correlated multi-column data
- join output sorted by columns from different relations
- sort keys without direct table statistics

These are required before claiming planner-based `mkqsApplicable` is safe.

### Data sizes

Run at multiple sizes:

- 100k rows for quick iteration
- 500k rows for continuity with previous tests
- larger datasets if runtime is acceptable

Avoid relying only on 100k rows because small datasets may exaggerate overheads
or cache effects.

## Implementation Improvement Plan

### Step 1: Improve reporting before changing code

Produce a revised report that includes:

- A/A noise for each major case
- bare-metal hardware and OS details
- build configuration
- median and dispersion, not only individual runtimes
- perf counters for largest gain/regression
- clear distinction between mksort disabled, mksort enabled, and planner
  selected cases

This directly addresses John's methodology concern.

### Step 2: Isolate classic path regression

Create minimal patch variants:

1. Remove mksort dispatch from `tuplesort_sort_memtuples`.
2. Keep dispatch but make it statically false.
3. Keep only planner/instrumentation changes.

Run these against master. The goal is to determine whether classic-path
regression comes from measurement noise, code layout, dispatch, or unrelated
changes.

### Step 3: Redesign compare abstraction around depth

Replace the current split between `mkqsGetDatumFunc`, tiebreak functions, and
duplicate handlers with a more general depth-range comparator:

```c
comparetup_mk(state, tuple1, tuple2, start_depth, max_depth)
```

Desired properties:

- compare a single depth when `start_depth == max_depth`
- compare a range of depths for final ordering
- allow btree to handle TID comparison internally when depth exceeds last key
- keep btree-specific duplicate logic out of generic mksort
- make pre-ordered checks easier to reason about

This matches John's architectural suggestion.

### Step 4: Move branches out of the hot path

Specialize paths based on known recursion state:

- depth zero vs depth greater than zero
- abbreviated key active vs inactive
- NULL partition separated vs mixed
- heap tuple vs btree index tuple
- generic comparator vs integer shortcut comparator

The goal is not necessarily to add a full macro template. The first target is
to stop checking conditions on every comparison when those conditions are known
for the current partition.

### Step 5: Clarify and retune small-array handling

Rename the small-array code to insertion sort if that is what it is.

Test thresholds systematically:

- 7
- 10
- 12
- 16
- 20
- 24

Run both standard qsort and mksort with comparable thresholds where possible.
Do not claim an algorithmic win if the result mostly comes from a better-tuned
threshold.

### Step 6: Make planner selection conservative

Do not rely on `stadistinct` as a strong guarantee.

Possible policy:

- select mksort only when the estimated benefit is clearly large
- require multiple sort keys
- require available and fresh-enough statistics
- avoid expression keys and complex filtered cases unless confidence is high
- preserve a GUC during development and possibly as an emergency escape hatch

The planner selection should be presented as a heuristic, not as proof of a
bounded regression.

## Suggested Response Direction to Reviewers

The next email to the thread should avoid defending the existing "5% error
range" wording. A stronger response would say:

- The previous wording understated the issue.
- A/A testing will be added to quantify noise.
- Bare-metal tests will be reported.
- The report will distinguish disabled mksort, enabled mksort, and planner
  selected mksort.
- New cases will cover first-key unique, first-key duplicate with later
  duplicates, first-key duplicate with second-key near unique, and single-key
  sanity checks.
- Perf counters and internal counters will be added for biggest gain/regression
  cases.
- The code will be refactored toward a depth-range compare abstraction and less
  branch-heavy hot paths.

## Working Hypotheses

1. If classic sort still regresses by about 5% on bare metal with low A/A noise,
   the cause is likely code layout, dispatch overhead, or unrelated patch
   changes.

2. If classic sort regression disappears on bare metal, the previous 5% result
   was primarily measurement noise from the VM or non-dedicated machine.

3. If mksort regression correlates with higher branch misses, John's hot-path
   branch concern is confirmed.

4. If mksort regression correlates with higher instruction count but not branch
   misses, repeated datum extraction, pre-ordered checks, or extra comparisons
   are more likely.

5. If planner-selected mksort avoids regressions only on ideal data but fails
   on filtered or correlated data, `stadistinct` is not sufficient as a
   selection criterion.

## Immediate Next Steps

1. Prepare the AMD AI 9 HX 370 bare-metal machine for stable performance
   testing.

2. Create or update the benchmark script to support:
   - interleaved variants
   - 30-50 repetitions
   - CSV output
   - median and dispersion calculation
   - optional `perf stat`
   - explicit `enable_mk_sort` and `mkqsApplicable` reporting

3. Run A/A tests on master.

4. Run A/B/C tests for master, patch with mksort off, and patch with mksort on.

5. Collect perf counters for the largest benefit and regression cases.

6. Add temporary internal mksort counters.

7. Build a small patch series for architecture cleanup:
   - depth-range compare API
   - btree TID handling moved back into btree-specific comparator
   - hot-path branch reduction
   - small-array threshold retuning

8. Send an updated report to the mailing list after the benchmark noise is
   quantified and the largest regressions have hardware-counter explanations.

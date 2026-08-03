/*
 * MK qsort (multi-key quick sort) is an alternative of standard qsort
 * algorithm, which has better performance for particular sort scenarios, i.e.
 * the data set has multiple keys to be sorted.
 *
 * The sorting algorithm blends Quicksort and radix sort; Like regular
 * Quicksort, it partitions its input into sets less than and greater than a
 * given value; like radix sort, it moves on to the next field once the current
 * input is known to be equal in the given field.
 *
 * The implementation is based on the paper:
 *   Jon L. Bentley and Robert Sedgewick, "Fast Algorithms for Sorting and
 *   Searching Strings", Jan 1997
 *
 * Some improvements which is related to additional handling for equal tuples
 * have been adapted to keep consistency with the implementations of postgres
 * qsort.
 *
 * For now, mk_qsort_tuple() is called in tuplesort_sort_memtuples() as a
 * replacement of qsort_tuple() when specific conditions are satisfied.
 */

/* Boundaries of the equal, lesser, unprocessed, and greater partitions. */
typedef struct MkqsPartitionBounds
{
	int			lessStart;
	int			lessEnd;
	int			greaterStart;
	int			greaterEnd;
} MkqsPartitionBounds;

/*
 * compare_tuple and partition are selected at the start of each recursive
 * level.  Heap tuples use direct integer comparators when the current sort key
 * has a recognized, non-abbreviated comparator; all other keys use their
 * generic SortSupport comparator.  Index tuples retain their representation-
 * specific generic path.
 */
typedef int (*MkqsCompareTuple) (SortTuple *a, SortTuple *b, int depth,
								 Tuplesortstate *state);
typedef bool (*MkqsPartition) (SortTuple *x, size_t n, int depth,
							   Tuplesortstate *state,
							   MkqsPartitionBounds *bounds);

/* Swap two tuples in the sort tuple array. */
static pg_attribute_always_inline void
mkqs_swap(int a,
		  int b,
		  SortTuple *x)
{
	SortTuple	t;

	if (a == b)
		return;
	t = x[a];
	x[a] = x[b];
	x[b] = t;
}

/* Swap two equally sized ranges in the sort tuple array. */
static inline void
mkqs_vec_swap(int a,
			  int b,
			  int size,
			  SortTuple *x)
{
	while (size-- > 0)
	{
		mkqs_swap(a, b, x);
		a++;
		b++;
	}
}

/* Extract the current sort-key datum from one heap SortTuple. */
static pg_attribute_always_inline Datum
mkqs_get_heap_datum(SortTuple *tuple, SortSupport sortKey,
					Tuplesortstate *state, bool *isNull)
{
	HeapTupleData heapTuple;
	TupleDesc	tupDesc = (TupleDesc) state->base.arg;

	heapTuple.t_len = ((MinimalTuple) tuple->tuple)->t_len +
		MINIMAL_TUPLE_OFFSET;
	heapTuple.t_data = (HeapTupleHeader) ((char *) tuple->tuple -
										  MINIMAL_TUPLE_OFFSET);

	if (likely(sortKey->ssup_attno > 0))
		return fastgetattr(&heapTuple, sortKey->ssup_attno, tupDesc, isNull);

	return heap_getattr(&heapTuple, sortKey->ssup_attno, tupDesc, isNull);
}

/* Extract the current sort-key datum from one btree index tuple. */
static pg_attribute_always_inline Datum
mkqs_get_index_datum(SortTuple *tuple, SortSupport sortKey,
					 Tuplesortstate *state, bool *isNull)
{
	int			depth = sortKey - state->base.sortKeys;

	Assert(tuple);
	Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
	Assert(state->base.mkqsIndexTupDesc != NULL);

	return index_getattr((IndexTuple) tuple->tuple, depth + 1,
						 state->base.mkqsIndexTupDesc, isNull);
}

/* Compare two non-NULL full datums after an abbreviated-key collision. */
static pg_attribute_always_inline int
mkqs_compare_abbrev_full_datum(Datum datum1, Datum datum2,
							   SortSupport sortKey)
{
	int			compare;

	compare = sortKey->abbrev_full_comparator(datum1, datum2, sortKey);
	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(compare);
	return compare;
}

/* Compare two non-NULL generic datums in the natural sort direction. */
static pg_attribute_always_inline int
mkqs_compare_datum_generic(Datum datum1, Datum datum2,
						   SortSupport sortKey)
{
	return sortKey->comparator(datum1, datum2, sortKey);
}

/*
 * Typed comparators keep the SortSupport argument to share one template
 * interface with the generic comparator; the compiler removes the unused
 * argument after inlining.
 */

#if SIZEOF_DATUM >= 8
/* Compare two non-NULL signed 64-bit datums in the natural direction. */
static pg_attribute_always_inline int
mkqs_compare_datum_int64(Datum datum1, Datum datum2,
						 SortSupport sortKey)
{
	int64		value1;
	int64		value2;

	value1 = DatumGetInt64(datum1);
	value2 = DatumGetInt64(datum2);
	return value1 < value2 ? -1 : value1 > value2 ? 1 : 0;
}

/* Compare two non-NULL unsigned 64-bit datums in the natural direction. */
static pg_attribute_always_inline int
mkqs_compare_datum_uint64(Datum datum1, Datum datum2,
						  SortSupport sortKey)
{
	uint64		value1;
	uint64		value2;

	value1 = DatumGetUInt64(datum1);
	value2 = DatumGetUInt64(datum2);
	return value1 < value2 ? -1 : value1 > value2 ? 1 : 0;
}
#endif

/* Compare two non-NULL signed 32-bit datums in the natural direction. */
static pg_attribute_always_inline int
mkqs_compare_datum_int32(Datum datum1, Datum datum2,
						 SortSupport sortKey)
{
	int32		value1;
	int32		value2;

	value1 = DatumGetInt32(datum1);
	value2 = DatumGetInt32(datum2);
	return value1 < value2 ? -1 : value1 > value2 ? 1 : 0;
}

#define MKQS_BASE_NAME heap_generic
#define MKQS_GET_DATUM mkqs_get_heap_datum
#define MKQS_COMPARE_DATUM mkqs_compare_datum_generic
#define MKQS_USE_ABBREVIATION 1
#include "mk_qsort_tuple_template.h"

#if SIZEOF_DATUM >= 8
#define MKQS_BASE_NAME heap_int64
#define MKQS_GET_DATUM mkqs_get_heap_datum
#define MKQS_COMPARE_DATUM mkqs_compare_datum_int64
#define MKQS_USE_ABBREVIATION 0
#include "mk_qsort_tuple_template.h"

#define MKQS_BASE_NAME heap_uint64
#define MKQS_GET_DATUM mkqs_get_heap_datum
#define MKQS_COMPARE_DATUM mkqs_compare_datum_uint64
#define MKQS_USE_ABBREVIATION 0
#include "mk_qsort_tuple_template.h"
#endif

#define MKQS_BASE_NAME heap_int32
#define MKQS_GET_DATUM mkqs_get_heap_datum
#define MKQS_COMPARE_DATUM mkqs_compare_datum_int32
#define MKQS_USE_ABBREVIATION 0
#include "mk_qsort_tuple_template.h"

#define MKQS_BASE_NAME index_btree
#define MKQS_GET_DATUM mkqs_get_index_datum
#define MKQS_COMPARE_DATUM mkqs_compare_datum_generic
#define MKQS_USE_ABBREVIATION 1
#include "mk_qsort_tuple_template.h"

/* Select the generated operations for one tuple representation and depth. */
static pg_attribute_always_inline void
mkqs_select_compare_funcs(Tuplesortstate *state, int depth,
						  MkqsCompareTuple *compare_tuple,
						  MkqsPartition *partition)
{
	SortSupport sortKey = &state->base.sortKeys[depth];

	if (state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE)
	{
		*compare_tuple = mkqs_compare_tuple_index_btree;
		*partition = mkqs_partition_index_btree;
		return;
	}

	Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_HEAP);
	*compare_tuple = mkqs_compare_tuple_heap_generic;
	*partition = mkqs_partition_heap_generic;

	/* Abbreviated leading datums require the generic fallback comparator. */
	if (sortKey->abbrev_converter)
		return;

	if (sortKey->comparator == ssup_datum_int32_cmp)
	{
		*compare_tuple = mkqs_compare_tuple_heap_int32;
		*partition = mkqs_partition_heap_int32;
	}
#if SIZEOF_DATUM >= 8
	else if (sortKey->comparator == ssup_datum_signed_cmp)
	{
		*compare_tuple = mkqs_compare_tuple_heap_int64;
		*partition = mkqs_partition_heap_int64;
	}
	else if (sortKey->comparator == ssup_datum_unsigned_cmp)
	{
		*compare_tuple = mkqs_compare_tuple_heap_uint64;
		*partition = mkqs_partition_heap_uint64;
	}
#endif
}

/* Compare two tuples over the inclusive range of sort-key depths. */
static pg_attribute_always_inline int
mkqs_compare_tuple_range(SortTuple *a, SortTuple *b,
						 int start_depth, int max_depth,
						 Tuplesortstate *state)
{
	for (int depth = start_depth; depth <= max_depth; depth++)
	{
		MkqsCompareTuple compare_tuple;
		MkqsPartition partition;
		int			compare;

		mkqs_select_compare_funcs(state, depth, &compare_tuple, &partition);
		compare = compare_tuple(a, b, depth, state);
		if (compare != 0)
			return compare;
	}

	return 0;
}

/* Check the ordering covered by the caller-supplied full comparator. */
static bool
mkqs_full_order_presorted(SortTuple *x, size_t n, Tuplesortstate *state,
						  SortTupleComparator compare)
{
	Assert(state->base.nKeys > 0);
	Assert(compare);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		if (compare(x + i - 1, x + i, state) > 0)
			return false;
	}

	return true;
}

/*
 * Check only the current depth.  Equality is not sufficient to return from
 * mksort because later depths have not been checked; equal groups still need
 * to recurse to the next depth. So only strictly increasing is to be checked.
 */
static bool
mkqs_depth_strictly_increasing(SortTuple *x, size_t n, int depth,
							   Tuplesortstate *state,
							   MkqsCompareTuple compare_tuple)
{
	Assert(depth >= 0);
	Assert(depth < state->base.nKeys);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		if (compare_tuple(x + i - 1, x + i, depth, state) >= 0)
			return false;
	}

	return true;
}

/* Return the index of the median of x[a], x[b], and x[c] at this depth. */
static pg_noinline int
get_median_from_three(int a,
					  int b,
					  int c,
					  SortTuple *x,
					  int depth,
					  Tuplesortstate *state,
					  MkqsCompareTuple compare_tuple)
{
	return compare_tuple(x + a, x + b, depth, state) < 0 ?
		(compare_tuple(x + b, x + c, depth, state) < 0 ? b :
		 (compare_tuple(x + a, x + c, depth, state) < 0 ? c : a)) :
		(compare_tuple(x + b, x + c, depth, state) > 0 ? b :
		 (compare_tuple(x + a, x + c, depth, state) < 0 ? a : c));
}

/*
 * Recursively sort x at one key depth using three-way partitioning.
 *
 * Select compare_tuple and partition for the current depth at each recursive
 * entry.  seenNull records whether any preceding equal key was NULL, which
 * the terminal duplicate handler needs for uniqueness checks.
 */
static void
mk_qsort_tuple_impl(SortTuple *x,
					size_t n,
					int depth,
					Tuplesortstate *state,
					bool seenNull)
{
	/*
	 * During partitioning, the four indexes delimit the ranges [0,
	 * lessStart), [lessStart, lessEnd), [lessEnd, greaterStart],
	 * (greaterStart, greaterEnd], and (greaterEnd, n).  From left to right,
	 * these contain values equal to the pivot, less than the pivot,
	 * unprocessed, greater than the pivot, and equal to the pivot.
	 */
	int			lessStart,
				lessEnd,
				greaterStart,
				greaterEnd,
				tupCount,
				m,
				l,
				r,
				d;
	int32		dist;
	bool		isDatumNull;
	MkqsCompareTuple compare_tuple;
	MkqsPartitionBounds bounds;
	MkqsPartition partition;

	Assert(depth <= state->base.nKeys);
	Assert(state->base.sortKeys);
	if (n <= 1)
		return;

	/* If we have reached the maximum depth, return immediately. */
	if (depth == state->base.nKeys)
		return;

	mkqs_select_compare_funcs(state, depth, &compare_tuple, &partition);

	CHECK_FOR_INTERRUPTS();

	/*
	 * Small inputs are cheaper to finish directly than to scan once and then
	 * run insertion sort over the same tuples.
	 */
	if (n < MKQS_INSERTION_SORT_THRESHOLD &&
		!state->base.mkqsHandleDupFunc)
	{
		for (m = 0; m < n; m++)
			for (l = m; l > 0; l--)
			{
				if (mkqs_compare_tuple_range(x + l - 1, x + l, depth,
											 state->base.nKeys - 1,
											 state) <= 0)
					break;
				mkqs_swap(l, l - 1, x);
			}
		return;
	}

	if (depth > 0)
	{
		/* Check whether the current depth is already strictly increasing. */
		if (mkqs_depth_strictly_increasing(x, n, depth, state,
										   compare_tuple))
			return;
	}

	/* Select a median-of-three/pseudomedian pivot and move it to x[0]. */
	m = n / 2;
	l = 0;
	r = n - 1;
	if (n > 40)
	{
		d = n / 8;
		l = get_median_from_three(l, l + d, l + 2 * d, x, depth,
								  state, compare_tuple);
		m = get_median_from_three(m - d, m, m + d, x, depth,
								  state, compare_tuple);
		r = get_median_from_three(r - 2 * d, r - d, r, x, depth,
								  state, compare_tuple);
	}
	lessStart = get_median_from_three(l, m, r, x, depth, state,
									  compare_tuple);
	mkqs_swap(0, lessStart, x);

	isDatumNull = partition(x, n, depth, state, &bounds);

	lessStart = bounds.lessStart;
	lessEnd = bounds.lessEnd;
	greaterStart = bounds.greaterStart;
	greaterEnd = bounds.greaterEnd;

	/*
	 * The unprocessed range is now empty, leaving the left-equal, lesser,
	 * greater, and right-equal ranges.  Move both equal ranges to the middle.
	 */

	/* Move the left equal part to the middle. */
	dist = Min(lessStart, lessEnd - lessStart);
	mkqs_vec_swap(0, lessEnd - dist, dist, x);

	/* Move the right equal part to the middle. */
	dist = Min(greaterEnd - greaterStart, n - greaterEnd - 1);
	mkqs_vec_swap(lessEnd, n - dist, dist, x);

	/*
	 * The array now has lesser, equal, and greater parts; the lesser or
	 * greater part may be empty.
	 */

	/* Recursively sort the lesser part at the same depth. */
	dist = lessEnd - lessStart;
	mk_qsort_tuple_impl(x,
						dist,
						depth,
						state,
						seenNull);

	/*
	 * Recurse to the next depth for the equal part.  Since every tuple in
	 * this part has the same current datum, the pivot's NULL flag represents
	 * the whole part.
	 */
	tupCount = lessStart + n - greaterEnd - 1;

	if (depth < state->base.nKeys - 1)
	{
		mk_qsort_tuple_impl(x + dist,
							tupCount,
							depth + 1,
							state,
							seenNull || isDatumNull);
	}
	else
	{
		/*
		 * At the final key, pass duplicate groups to the tuple-type-specific
		 * handler for work such as uniqueness checks or TID ordering.
		 */
		if (state->base.mkqsHandleDupFunc &&
			(tupCount > 1))
		{
			state->base.mkqsHandleDupFunc(x + dist,
										  tupCount,
										  seenNull || isDatumNull,
										  state);
		}
	}

	/* Recursively sort the greater part at the same depth. */
	dist = greaterEnd - greaterStart;
	mk_qsort_tuple_impl(x + n - dist,
						dist,
						depth,
						state,
						seenNull);

}

/*
 * Check the complete remaining order before entering recursive mksort.
 * Direct mksort enters at depth 0 and needs the ordinary comparator.  Radix
 * sort enters at depth 1 after grouping equal leading keys, so its tiebreak
 * comparator covers the complete remaining order.
 *
 * The latter check matters for btree builds where every explicit key in a
 * radix group is equal but the heap TIDs are already ordered.  Standard
 * qsort's presort check returns after one scan in that case.  Without the
 * same check here, mksort partitions the group once per remaining equal key
 * and then invokes another qsort for the TIDs.
 */
static void
mk_qsort_tuple(SortTuple *x,
			   size_t n,
			   int depth,
			   Tuplesortstate *state,
			   bool seenNull)
{
	SortTupleComparator compare;

	Assert(depth == 0 || depth == 1);
	compare = depth == 0 ? state->base.comparetup :
		state->base.comparetup_tiebreak;

	if (mkqs_full_order_presorted(x, n, state, compare))
		return;

	state->mkqsUsed = true;
	Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_HEAP ||
		   state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
	mk_qsort_tuple_impl(x, n, depth, state, seenNull);
}

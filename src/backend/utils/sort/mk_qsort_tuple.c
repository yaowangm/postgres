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

#define MKQS_COMPARE_NONNULL 2

/* Boundaries of the equal, lesser, unprocessed, and greater partitions. */
typedef struct MkqsPartitionBounds
{
	int			lessStart;
	int			lessEnd;
	int			greaterStart;
	int			greaterEnd;
} MkqsPartitionBounds;

static pg_attribute_always_inline int comparetup_mk(SortTuple *a,
												  SortTuple *b,
												  int start_depth, int max_depth,
												  Tuplesortstate *state);

/* Swap two tuples in sort tuple array */
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

/* Swap tuples by batch in sort tuple array */
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

/*
 * Extract one or two datums at the given depth from btree index tuples.
 * When x2 is NULL, only the first datum is returned.
 */
static pg_attribute_always_inline void
mkqs_get_index_datums(const SortTuple *x1,
					 const SortTuple *x2,
					 int depth,
					 Tuplesortstate *state,
					 Datum *datum1,
					 bool *isNull1,
					 Datum *datum2,
					 bool *isNull2)
{
	Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
	mkqs_get_datum_index_btree(x1, x2, depth, state,
								 datum1, isNull1, datum2, isNull2);
}

/*
 * Check whether current datum (at specified tuple and depth) is null
 * Note that the input x means a specified tuple provided by caller but not
 * a tuple array, so tupleIndex is unnecessary.
 */
static inline bool
check_datum_null(SortTuple *x,
				 int depth,
				 Tuplesortstate *state)
{
	Datum		datum;
	bool		isNull;

	Assert(depth < state->base.nKeys);

	if (depth == 0)
		return x->isnull1;

	if (state->base.mkqsTupleType == MKQS_TUPLE_TYPE_HEAP)
	{
		HeapTupleData heapTuple;
		SortSupport sortKey = &state->base.sortKeys[depth];

		heapTuple.t_len = ((MinimalTuple) x->tuple)->t_len +
			MINIMAL_TUPLE_OFFSET;
		heapTuple.t_data = (HeapTupleHeader) ((char *) x->tuple -
			MINIMAL_TUPLE_OFFSET);
		datum = heap_getattr(&heapTuple, sortKey->ssup_attno,
							 (TupleDesc) state->base.arg, &isNull);
	}
	else
		mkqs_get_index_datums(x, NULL, depth, state,
							 &datum, &isNull, NULL, NULL);

	return isNull;
}

/*
 * Compare NULL states according to sortKey.  Return MKQS_COMPARE_NONNULL when
 * both datums must be compared.
 */
static pg_attribute_always_inline int
mkqs_compare_nulls(bool isNull1, bool isNull2, SortSupport sortKey)
{
	if (!isNull1 && !isNull2)
		return MKQS_COMPARE_NONNULL;

	if (isNull1 && isNull2)
		return 0;

	if (isNull1 == sortKey->ssup_nulls_first)
		return -1;

	return 1;
}

/* Extract the current sort-key datum from one heap tuple. */
static pg_attribute_always_inline Datum
mkqs_get_heap_datum(SortTuple *tuple, SortSupport sortKey,
					Tuplesortstate *state, bool *isNull)
{
	HeapTupleData heapTuple;

	heapTuple.t_len = ((MinimalTuple) tuple->tuple)->t_len +
		MINIMAL_TUPLE_OFFSET;
	heapTuple.t_data = (HeapTupleHeader) ((char *) tuple->tuple -
		MINIMAL_TUPLE_OFFSET);
	return heap_getattr(&heapTuple, sortKey->ssup_attno,
						(TupleDesc) state->base.arg, isNull);
}

/* Extract the current sort-key datum from one btree index tuple. */
static pg_attribute_always_inline Datum
mkqs_get_index_datum_by_sortkey(SortTuple *tuple, SortSupport sortKey,
								Tuplesortstate *state, bool *isNull)
{
	int			depth = sortKey - state->base.sortKeys;
	Datum		datum;

	mkqs_get_index_datums(tuple, NULL, depth, state,
						 &datum, isNull, NULL, NULL);
	return datum;
}

#if SIZEOF_DATUM >= 8
#define MKQS_COMPARE mkqs_compare_heap_signed
#define MKQS_PARTITION mkqs_partition_heap_signed
#define MKQS_COMPARE_TYPE int64
#define MKQS_COMPARE_DATUM_GETTER DatumGetInt64
#define MKQS_COMPARE_GET_DATUM mkqs_get_heap_datum
#include "mk_qsort_tuple_compare_template.h"

#define MKQS_COMPARE mkqs_compare_heap_unsigned
#define MKQS_PARTITION mkqs_partition_heap_unsigned
#define MKQS_COMPARE_TYPE uint64
#define MKQS_COMPARE_DATUM_GETTER DatumGetUInt64
#define MKQS_COMPARE_GET_DATUM mkqs_get_heap_datum
#include "mk_qsort_tuple_compare_template.h"
#endif

#define MKQS_COMPARE mkqs_compare_heap_int32
#define MKQS_PARTITION mkqs_partition_heap_int32
#define MKQS_COMPARE_TYPE int32
#define MKQS_COMPARE_DATUM_GETTER DatumGetInt32
#define MKQS_COMPARE_GET_DATUM mkqs_get_heap_datum
#include "mk_qsort_tuple_compare_template.h"

#if SIZEOF_DATUM >= 8
#define MKQS_COMPARE mkqs_compare_index_signed
#define MKQS_PARTITION mkqs_partition_index_signed
#define MKQS_COMPARE_TYPE int64
#define MKQS_COMPARE_DATUM_GETTER DatumGetInt64
#define MKQS_COMPARE_GET_DATUM mkqs_get_index_datum_by_sortkey
#include "mk_qsort_tuple_compare_template.h"

#define MKQS_COMPARE mkqs_compare_index_unsigned
#define MKQS_PARTITION mkqs_partition_index_unsigned
#define MKQS_COMPARE_TYPE uint64
#define MKQS_COMPARE_DATUM_GETTER DatumGetUInt64
#define MKQS_COMPARE_GET_DATUM mkqs_get_index_datum_by_sortkey
#include "mk_qsort_tuple_compare_template.h"
#endif

#define MKQS_COMPARE mkqs_compare_index_int32
#define MKQS_PARTITION mkqs_partition_index_int32
#define MKQS_COMPARE_TYPE int32
#define MKQS_COMPARE_DATUM_GETTER DatumGetInt32
#define MKQS_COMPARE_GET_DATUM mkqs_get_index_datum_by_sortkey
#include "mk_qsort_tuple_compare_template.h"

/* Compare a heap tuple with a previously extracted pivot datum. */
static pg_attribute_always_inline int
mkqs_compare_heap_generic_to_pivot(SortTuple *tuple, Datum pivotDatum,
								   bool pivotIsNull,
								   SortSupport sortKey,
								   Tuplesortstate *state)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_heap_datum(tuple, sortKey, state, &isNull);

	return ApplySortComparator(datum, isNull,
							   pivotDatum, pivotIsNull,
							   sortKey);
}

/* Compare a btree index tuple with a previously extracted pivot datum. */
static pg_attribute_always_inline int
mkqs_compare_index_generic_to_pivot(SortTuple *tuple, Datum pivotDatum,
									bool pivotIsNull,
									SortSupport sortKey,
									Tuplesortstate *state)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_index_datum_by_sortkey(tuple, sortKey, state, &isNull);

	return ApplySortComparator(datum, isNull,
							   pivotDatum, pivotIsNull,
							   sortKey);
}

/*
 * Keep the generic comparator in the caller's code path.  Unlike the typed
 * cases, it does not benefit from dispatching to a specialized partition.
 */
#define MKQS_PARTITION mkqs_partition_generic
#define MKQS_PARTITION_SCOPE static pg_attribute_always_inline
#define MKQS_PARTITION_COMPARE(tuple) \
	comparetup_mk((tuple), pivot, depth, depth, state)
#include "mk_qsort_tuple_partition_template.h"

/* Cache the pivot datum for generic btree index partitions. */
#define MKQS_PARTITION mkqs_partition_index_generic
#define MKQS_PARTITION_SCOPE static pg_attribute_always_inline
#define MKQS_PARTITION_EXTRA_DECLARATIONS \
	SortSupport sortKey; \
	Datum		pivotDatum; \
	bool		pivotIsNull;
#define MKQS_PARTITION_SETUP() \
	do { \
		sortKey = &state->base.sortKeys[depth]; \
		pivotDatum = mkqs_get_index_datum_by_sortkey(pivot, sortKey, state, \
												 &pivotIsNull); \
	} while (0)
#define MKQS_PARTITION_COMPARE(tuple) \
	mkqs_compare_index_generic_to_pivot((tuple), pivotDatum, pivotIsNull, \
										sortKey, state)
#include "mk_qsort_tuple_partition_template.h"

/*
 * Heap generic comparators need neither tuple-representation dispatch nor
 * integer comparator detection once recursion has selected this depth.
 */
#define MKQS_PARTITION mkqs_partition_heap_generic
#define MKQS_PARTITION_SCOPE static pg_attribute_always_inline
#define MKQS_PARTITION_EXTRA_DECLARATIONS \
	SortSupport sortKey; \
	Datum		pivotDatum; \
	bool		pivotIsNull;
#define MKQS_PARTITION_SETUP() \
	do { \
		sortKey = &state->base.sortKeys[depth]; \
		pivotDatum = mkqs_get_heap_datum(pivot, sortKey, state, \
										&pivotIsNull); \
	} while (0)
#define MKQS_PARTITION_COMPARE(tuple) \
	mkqs_compare_heap_generic_to_pivot((tuple), pivotDatum, pivotIsNull, \
									   sortKey, state)
#include "mk_qsort_tuple_partition_template.h"

/*
 * Compare two tuples (index btree type) at specified depth
 *
 * If "abbreviated key" is disabled:
 *   get specified datums and compare them by ApplySortComparator().
 * If "abbreviated key" is enabled:
 *   Only first datum may be abbr key according to the design (see the comments
 *   of struct SortTuple), so different operations are needed for different
 *   datum.
 *   For first datum (depth == 0): get first datums ("abbr key" version) and
 *   compare them by ApplySortComparator(). If they are equal, get "full"
 *   version and compare again by ApplySortAbbrevFullComparator().
 *   For other datums: get specified datums and compare them by
 *   ApplySortComparator() as regular routine does.
 *
 * See comparetup_heap() for details.
 */
static pg_attribute_always_inline int
comparetup_mk_index_btree_single(SortTuple *tuple1,
								 SortTuple *tuple2,
								 int depth,
								 Tuplesortstate *state)
{
	Datum		datum1,
				datum2;
	bool		isNull1,
				isNull2;
	SortSupport sortKey;
	int			ret = 0;

	Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
	Assert(depth < state->base.nKeys);

	sortKey = state->base.sortKeys + depth;
	mkqs_get_index_datums(tuple1, tuple2, depth, state,
						 &datum1, &isNull1, &datum2, &isNull2);

	/*
	 * If "abbreviated key" is enabled, and we are in the first depth, it
	 * means only "abbreviated keys" was compared. If the two datums were
	 * determined to be equal by ApplySortComparator() in
	 * comparetup_mk(), we need to perform an extra "full" comparing
	 * by ApplySortAbbrevFullComparator().
	 */
	if (sortKey->abbrev_converter &&
		depth == 0)
	{
		ret = ApplySortAbbrevFullComparator(datum1,
											isNull1,
											datum2,
											isNull2,
											sortKey);
	}
	else
	{
		ret = ApplySortComparator(datum1, isNull1,
								  datum2, isNull2, sortKey);
	}

	return ret;
}

/* Compare an inclusive range of heap tuple sort-key depths. */
static inline int
comparetup_mk_heap(SortTuple *a, SortTuple *b,
				   int start_depth, int max_depth,
				   Tuplesortstate *state)
{
	TuplesortPublic *base = &state->base;
	HeapTupleData ltup;
	HeapTupleData rtup;
	TupleDesc	tupDesc = (TupleDesc) base->arg;
	int			depth = start_depth;
	int32		compare;

	Assert(start_depth >= 0);
	Assert(start_depth <= max_depth);
	Assert(max_depth < base->nKeys);

	if (depth == 0)
	{
		SortSupport sortKey = &base->sortKeys[0];

		/*
		 * datum1 contains either the full leading key or its abbreviated
		 * representation.  A nonzero abbreviated comparison is conclusive,
		 * but zero does not establish that the full values are equal.
		 */
		compare = ApplySortComparator(a->datum1, a->isnull1,
								  b->datum1, b->isnull1, sortKey);
		if (compare != 0)
			return compare;

		if (!sortKey->abbrev_converter)
		{
			if (max_depth == 0)
				return 0;
			depth = 1;
		}
		else if (a->isnull1 || b->isnull1)
		{
			/* Both leading keys are NULL, so no full comparison is needed. */
			Assert(a->isnull1 && b->isnull1);
			if (max_depth == 0)
				return 0;
			depth = 1;
		}
	}

	ltup.t_len = ((MinimalTuple) a->tuple)->t_len + MINIMAL_TUPLE_OFFSET;
	ltup.t_data = (HeapTupleHeader) ((char *) a->tuple - MINIMAL_TUPLE_OFFSET);
	rtup.t_len = ((MinimalTuple) b->tuple)->t_len + MINIMAL_TUPLE_OFFSET;
	rtup.t_data = (HeapTupleHeader) ((char *) b->tuple - MINIMAL_TUPLE_OFFSET);

	if (depth == 0)
	{
		SortSupport sortKey = &base->sortKeys[0];
		Datum		datum1;
		Datum		datum2;
		bool		isnull1;
		bool		isnull2;

		/*
		 * The abbreviated keys compared equal, so compare their full,
		 * necessarily non-NULL values.  Calling the comparator directly
		 * avoids repeating the NULL checks performed above.
		 */
		datum1 = heap_getattr(&ltup, sortKey->ssup_attno, tupDesc, &isnull1);
		datum2 = heap_getattr(&rtup, sortKey->ssup_attno, tupDesc, &isnull2);
		Assert(!isnull1 && !isnull2);
		compare = sortKey->abbrev_full_comparator(datum1, datum2, sortKey);
		if (compare != 0 || max_depth == 0)
		{
			if (sortKey->ssup_reverse)
				INVERT_COMPARE_RESULT(compare);
			return compare;
		}
		depth = 1;
	}

	for (; depth <= max_depth; depth++)
	{
		SortSupport sortKey = &base->sortKeys[depth];
		Datum		datum1;
		Datum		datum2;
		bool		isnull1;
		bool		isnull2;

		datum1 = heap_getattr(&ltup, sortKey->ssup_attno, tupDesc, &isnull1);
		datum2 = heap_getattr(&rtup, sortKey->ssup_attno, tupDesc, &isnull2);
		compare = ApplySortComparator(datum1, isnull1,
									  datum2, isnull2, sortKey);
		if (compare != 0)
			return compare;
	}

	return 0;
}

/* Compare an inclusive range of btree index tuple sort-key depths. */
static int
comparetup_mk_index_btree_range(SortTuple *a, SortTuple *b,
							   int start_depth, int max_depth,
							   Tuplesortstate *state)
{
	int			depth = start_depth;
	int			compare;

	for (; depth <= max_depth; depth++)
	{
		compare = comparetup_mk_index_btree_single(a, b, depth, state);
		if (compare != 0)
			return compare;
	}

	return 0;
}

/* Compare the leading key inline before entering the range comparator. */
static pg_attribute_always_inline int
comparetup_mk_index_btree(SortTuple *a, SortTuple *b,
							 int start_depth, int max_depth,
							 Tuplesortstate *state)
{

	Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
	Assert(start_depth >= 0);
	Assert(start_depth <= max_depth);
	Assert(max_depth < state->base.nKeys);

	if (start_depth == 0)
	{
		SortSupport sortKey = &state->base.sortKeys[0];
		int			compare;

		compare = ApplySortComparator(a->datum1, a->isnull1,
								  b->datum1, b->isnull1, sortKey);
		if (compare != 0)
			return compare;

		if (state->base.sortKeys->abbrev_converter)
			return comparetup_mk_index_btree_range(a, b, 0, max_depth, state);

		if (max_depth == 0)
			return 0;

		start_depth = 1;
	}
	return comparetup_mk_index_btree_range(a, b, start_depth, max_depth, state);
}

/* Compare an inclusive range of sort-key depths. */
static pg_attribute_always_inline int
comparetup_mk(SortTuple *a, SortTuple *b,
			  int start_depth, int max_depth,
			  Tuplesortstate *state)
{
	if (state->base.mkqsTupleType == MKQS_TUPLE_TYPE_HEAP)
		return comparetup_mk_heap(a, b, start_depth, max_depth, state);

	return comparetup_mk_index_btree(a, b, start_depth, max_depth, state);
}

/*
 * Check whether the tuples are nondecreasing over the complete ordering.
 * Equality is safe because every depth that can affect the final order is
 * included.  Use the standard full comparator so this scan has the same cost
 * and semantics as qsort_tuple()'s presorted check.
 */
static bool
mkqs_full_order_presorted(SortTuple *x, size_t n, Tuplesortstate *state)
{
	Assert(state->base.nKeys > 0);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		if (COMPARETUP(state, x + i - 1, x + i) > 0)
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
							   Tuplesortstate *state)
{
	Assert(depth >= 0);
	Assert(depth < state->base.nKeys);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		if (comparetup_mk(x + i - 1, x + i,
							depth, depth, state) >= 0)
			return false;
	}

	return true;
}

/* Find the median of three values */
static pg_attribute_always_inline int
get_median_from_three(int a,
					  int b,
					  int c,
					  SortTuple *x,
					  int depth,
					  Tuplesortstate *state)
{
	return comparetup_mk(x + a, x + b, depth, depth, state) < 0 ?
			 (comparetup_mk(x + b, x + c, depth, depth, state) < 0 ?
				b : (comparetup_mk(x + a, x + c, depth, depth, state) < 0 ? c : a))
			 : (comparetup_mk(x + b, x + c, depth, depth, state) > 0 ?
				b : (comparetup_mk(x + a, x + c, depth, depth, state) < 0 ? a : c));
}

/*
 * Major of multi-key quick sort
 *
 * seenNull indicates whether we have seen NULL in any datum we checked
 */
static void
mk_qsort_tuple(SortTuple *x,
			   size_t n,
			   int depth,
			   Tuplesortstate *state,
			   bool seenNull)
{
	/*
	 * In the process, the tuple array consists of five parts: left equal,
	 * less, not-processed, greater, right equal
	 *
	 * lessStart indicates the first position of less part lessEnd indicates
	 * the next position after less part greaterStart indicates the prior
	 * position before greater part greaterEnd indicates the latest position
	 * of greater part the range between lessEnd and greaterStart (inclusive)
	 * is not-processed
	 */
	int			lessStart,
				lessEnd,
				greaterStart,
				greaterEnd,
				tupCount,
				m, l, r, d;
	int32		dist;
	bool		isDatumNull;
	MkqsPartitionBounds bounds;


	Assert(depth <= state->base.nKeys);
	Assert(state->base.sortKeys);
	Assert(state->base.mkqsTupleType != MKQS_TUPLE_TYPE_UNSUPPORTED);

	if (n <= 1)
		return;

	/* If we have exceeded the max depth, return immediately */
	if (depth == state->base.nKeys)
		return;

	state->mkqsUsed = true;

	CHECK_FOR_INTERRUPTS();


	if (depth == 0)
	{
		/* The caller may already have performed and failed this exact scan. */
		if (!state->mkqsTopPresortFailed &&
			mkqs_full_order_presorted(x, n, state))
			return;
	}
	else
	{
		/* For current depth, perform strictly increasing check */
		if (mkqs_depth_strictly_increasing(x, n, depth, state))
			return;
	}

	/*
	 * When the count < MKQS_INSERTION_SORT_THRESHOLD and no need to handle
     * duplicated tuples, use insert sort.
	 *
	 * Insert sort is not applicable for scenario of handle duplicated tuples
	 * because it is difficult to check NULL effectively.
	 *
	 * No need to check for interrupts since the data size is pretty small.
	 *
	 * TODO: Can we check NULL for insert sort with minimal cost?
	 */
	if (n < MKQS_INSERTION_SORT_THRESHOLD &&
		!state->base.mkqsHandleDupFunc)
	{
		for (m = 0;m < n;m++)
			for (l = m; l > 0; l--)
			{
				if (comparetup_mk(x + l - 1, x + l, depth,
								 state->base.nKeys - 1, state) <= 0)
					break;
				mkqs_swap(l, l - 1, x);
			}
		return;
	}

	/* Select pivot by random and move it to the first position */
	m = n / 2;
	l = 0;
	r = n - 1;
	if (n > 40)
	{
		d = n / 8;
		l = get_median_from_three(l, l + d, l + 2 * d, x, depth, state);
		m = get_median_from_three(m - d, m, m + d, x, depth, state);
		r = get_median_from_three(r - 2 * d, r - d, r, x, depth, state);
	}
	lessStart = get_median_from_three(l, m, r, x, depth, state);
	mkqs_swap(0, lessStart, x);

	if (depth == 0)
		mkqs_partition_generic(x, n, depth, state, &bounds);
	else if (state->base.mkqsTupleType == MKQS_TUPLE_TYPE_HEAP)
	{
		SortSupport sortKey = &state->base.sortKeys[depth];

#if SIZEOF_DATUM >= 8
		if (sortKey->comparator == ssup_datum_signed_cmp)
			mkqs_partition_heap_signed(x, n, depth, state, &bounds);
		else if (sortKey->comparator == ssup_datum_unsigned_cmp)
			mkqs_partition_heap_unsigned(x, n, depth, state, &bounds);
		else
#endif
		if (sortKey->comparator == ssup_datum_int32_cmp)
			mkqs_partition_heap_int32(x, n, depth, state, &bounds);
		else
			mkqs_partition_heap_generic(x, n, depth, state, &bounds);
	}
	else
	{
		SortSupport sortKey = &state->base.sortKeys[depth];

#if SIZEOF_DATUM >= 8
		if (sortKey->comparator == ssup_datum_signed_cmp)
			mkqs_partition_index_signed(x, n, depth, state, &bounds);
		else if (sortKey->comparator == ssup_datum_unsigned_cmp)
			mkqs_partition_index_unsigned(x, n, depth, state, &bounds);
		else
#endif
		if (sortKey->comparator == ssup_datum_int32_cmp)
			mkqs_partition_index_int32(x, n, depth, state, &bounds);
		else
			mkqs_partition_index_generic(x, n, depth, state, &bounds);
	}

	lessStart = bounds.lessStart;
	lessEnd = bounds.lessEnd;
	greaterStart = bounds.greaterStart;
	greaterEnd = bounds.greaterEnd;

	/*
	 * Now the array has four parts: left equal, lesser, greater, right equal
	 * Note greaterStart is less than lessEnd now
	 */

	/* Move the left equal part to middle */
	dist = Min(lessStart, lessEnd - lessStart);
	mkqs_vec_swap(0, lessEnd - dist, dist, x);

	/* Move the right equal part to middle */
	dist = Min(greaterEnd - greaterStart, n - greaterEnd - 1);
	mkqs_vec_swap(lessEnd, n - dist, dist, x);

	/*
	 * Now the array has three parts: lesser, equal, greater Note that one or
	 * two parts may have no element at all.
	 */

	/* Recursively sort the lesser part */

	/* dist means the size of less part */
	dist = lessEnd - lessStart;
	mk_qsort_tuple(x,
				   dist,
				   depth,
				   state,
				   seenNull);

	/* Recursively sort the equal part */

	/*
	 * (x + dist) means the first tuple in the equal part Since all tuples
	 * have equal datums at current depth, we just check any one of them to
	 * determine whether we have seen null datum.
	 */
	isDatumNull = check_datum_null(x + dist, depth, state);

	/* (lessStart + n - greaterEnd - 1) means the size of equal part */
	tupCount = lessStart + n - greaterEnd - 1;

	if (depth < state->base.nKeys - 1)
	{
		mk_qsort_tuple(x + dist,
					   tupCount,
					   depth + 1,
					   state,
					   seenNull || isDatumNull);
	}
	else
	{
		/*
		 * We have reach the max depth: Call mkqsHandleDupFunc to handle
		 * duplicated tuples if necessary, e.g. checking uniqueness or extra
		 * comparing
		 */

		/*
		 * Call mkqsHandleDupFunc if: 1. mkqsHandleDupFunc is filled 2. the
		 * size of equal part > 1
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

	/* Recursively sort the greater part */

	/* dist means the size of greater part */
	dist = greaterEnd - greaterStart;
	mk_qsort_tuple(x + n - dist,
				   dist,
				   depth,
				   state,
				   seenNull);

}

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

typedef int (*MkqsCompareDatumTyped) (Datum datum1, Datum datum2,
									  SortSupport sortKey);
typedef int (*MkqsCompareTuple) (SortTuple *a, SortTuple *b, int depth,
								 Tuplesortstate *state,
								 MkqsCompareDatumTyped compare_datum_typed);
typedef bool (*MkqsPartition) (SortTuple *x, size_t n, int depth,
							   Tuplesortstate *state,
							   MkqsCompareDatumTyped compare_datum_typed,
							   MkqsPartitionBounds *bounds);

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

/* Extract a sort-key datum from an already constructed heap tuple. */
static pg_attribute_always_inline Datum
mkqs_get_heap_tuple_datum(HeapTuple tuple, SortSupport sortKey,
						  TupleDesc tupDesc, bool *isNull)
{
	if (likely(sortKey->ssup_attno > 0))
		return fastgetattr(tuple, sortKey->ssup_attno, tupDesc, isNull);

	return heap_getattr(tuple, sortKey->ssup_attno, tupDesc, isNull);
}

/* Extract the current sort-key datum from one heap SortTuple. */
static pg_attribute_always_inline Datum
mkqs_get_heap_datum(SortTuple *tuple, SortSupport sortKey,
					Tuplesortstate *state, bool *isNull)
{
	HeapTupleData heapTuple;

	heapTuple.t_len = ((MinimalTuple) tuple->tuple)->t_len +
		MINIMAL_TUPLE_OFFSET;
	heapTuple.t_data = (HeapTupleHeader) ((char *) tuple->tuple -
										  MINIMAL_TUPLE_OFFSET);
	return mkqs_get_heap_tuple_datum(&heapTuple, sortKey,
									 (TupleDesc) state->base.arg, isNull);
}

/* Extract the current sort-key datum from one btree index tuple. */
static pg_attribute_always_inline Datum
mkqs_get_index_datum(SortTuple *tuple, SortSupport sortKey,
					 Tuplesortstate *state, bool *isNull)
{
	int			depth = sortKey - state->base.sortKeys;

	return mkqs_get_datum_index_btree(tuple, depth, state, isNull);
}

/* Apply NULL and direction semantics around one non-NULL datum comparator. */
static pg_attribute_always_inline int
mkqs_compare_datum(Datum datum1, bool isNull1,
				   Datum datum2, bool isNull2,
				   SortSupport sortKey,
				   MkqsCompareDatumTyped compare_datum_typed)
{
	int			compare;

	if (isNull1 || isNull2)
	{
		if (isNull1 && isNull2)
			return 0;
		return isNull1 == sortKey->ssup_nulls_first ? -1 : 1;
	}

	compare = compare_datum_typed(datum1, datum2, sortKey);
	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(compare);
	return compare;
}

static int
mkqs_compare_tuple_heap(SortTuple *a, SortTuple *b, int depth,
						Tuplesortstate *state,
						MkqsCompareDatumTyped compare_datum_typed)
{
	SortSupport sortKey = &state->base.sortKeys[depth];
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;
	int			compare;

	if (depth == 0)
	{
		compare = mkqs_compare_datum(a->datum1, a->isnull1,
									 b->datum1, b->isnull1,
									 sortKey, compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			a->isnull1 || b->isnull1)
			return compare;

		datum1 = mkqs_get_heap_datum(a, sortKey, state, &isNull1);
		datum2 = mkqs_get_heap_datum(b, sortKey, state, &isNull2);
		Assert(!isNull1 && !isNull2);
		return mkqs_compare_datum(datum1, false, datum2, false, sortKey,
								  sortKey->abbrev_full_comparator);
	}

	datum1 = mkqs_get_heap_datum(a, sortKey, state, &isNull1);
	datum2 = mkqs_get_heap_datum(b, sortKey, state, &isNull2);
	return mkqs_compare_datum(datum1, isNull1, datum2, isNull2, sortKey,
							  compare_datum_typed);
}

static int
mkqs_compare_tuple_index_btree(SortTuple *a, SortTuple *b, int depth,
							   Tuplesortstate *state,
							   MkqsCompareDatumTyped compare_datum_typed)
{
	SortSupport sortKey = &state->base.sortKeys[depth];
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;
	int			compare;

	if (depth == 0)
	{
		compare = mkqs_compare_datum(a->datum1, a->isnull1,
									 b->datum1, b->isnull1,
									 sortKey, compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			a->isnull1 || b->isnull1)
			return compare;

		datum1 = mkqs_get_index_datum(a, sortKey, state, &isNull1);
		datum2 = mkqs_get_index_datum(b, sortKey, state, &isNull2);
		Assert(!isNull1 && !isNull2);
		return mkqs_compare_datum(datum1, false, datum2, false, sortKey,
								  sortKey->abbrev_full_comparator);
	}

	datum1 = mkqs_get_index_datum(a, sortKey, state, &isNull1);
	datum2 = mkqs_get_index_datum(b, sortKey, state, &isNull2);
	return mkqs_compare_datum(datum1, isNull1, datum2, isNull2, sortKey,
							  compare_datum_typed);
}

static pg_attribute_always_inline int
mkqs_compare_heap_to_pivot(SortTuple *tuple, int depth,
						   Tuplesortstate *state, SortSupport sortKey,
						   MkqsCompareDatumTyped compare_datum_typed,
						   Datum pivotDatum, bool pivotIsNull,
						   Datum pivotFullDatum)
{
	Datum		datum;
	bool		isNull;
	int			compare;

	if (depth == 0)
	{
		compare = mkqs_compare_datum(tuple->datum1, tuple->isnull1,
									 pivotDatum, pivotIsNull,
									 sortKey, compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			tuple->isnull1 || pivotIsNull)
			return compare;

		datum = mkqs_get_heap_datum(tuple, sortKey, state, &isNull);
		Assert(!isNull);
		return mkqs_compare_datum(datum, false, pivotFullDatum, false,
								  sortKey, sortKey->abbrev_full_comparator);
	}

	datum = mkqs_get_heap_datum(tuple, sortKey, state, &isNull);
	return mkqs_compare_datum(datum, isNull, pivotDatum, pivotIsNull,
							  sortKey, compare_datum_typed);
}

static pg_attribute_always_inline int
mkqs_compare_index_btree_to_pivot(SortTuple *tuple, int depth,
								  Tuplesortstate *state, SortSupport sortKey,
								  MkqsCompareDatumTyped compare_datum_typed,
								  Datum pivotDatum, bool pivotIsNull,
								  Datum pivotFullDatum)
{
	Datum		datum;
	bool		isNull;
	int			compare;

	if (depth == 0)
	{
		compare = mkqs_compare_datum(tuple->datum1, tuple->isnull1,
									 pivotDatum, pivotIsNull,
									 sortKey, compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			tuple->isnull1 || pivotIsNull)
			return compare;

		datum = mkqs_get_index_datum(tuple, sortKey, state, &isNull);
		Assert(!isNull);
		return mkqs_compare_datum(datum, false, pivotFullDatum, false,
								  sortKey, sortKey->abbrev_full_comparator);
	}

	datum = mkqs_get_index_datum(tuple, sortKey, state, &isNull);
	return mkqs_compare_datum(datum, isNull, pivotDatum, pivotIsNull,
							  sortKey, compare_datum_typed);
}

/* Partition around x[0], comparing only the current key depth. */
static bool
mkqs_partition_heap(SortTuple *x, size_t n, int depth,
					Tuplesortstate *state,
					MkqsCompareDatumTyped compare_datum_typed,
					MkqsPartitionBounds *bounds)
{
	SortSupport sortKey = &state->base.sortKeys[depth];
	Datum		pivotDatum;
	Datum		pivotFullDatum = (Datum) 0;
	bool		pivotIsNull;
	int32		dist;

	if (depth == 0)
	{
		pivotDatum = x->datum1;
		pivotIsNull = x->isnull1;
		if (sortKey->abbrev_converter && !pivotIsNull)
		{
			bool		isNull;

			pivotFullDatum = mkqs_get_heap_datum(x, sortKey, state, &isNull);
			Assert(!isNull);
		}
	}
	else
		pivotDatum = mkqs_get_heap_datum(x, sortKey, state, &pivotIsNull);

	bounds->lessStart = 1;
	bounds->lessEnd = 1;
	bounds->greaterStart = n - 1;
	bounds->greaterEnd = n - 1;

	while (true)
	{
		CHECK_FOR_INTERRUPTS();

		while (bounds->lessEnd <= bounds->greaterStart)
		{
			dist = mkqs_compare_heap_to_pivot(x + bounds->lessEnd, depth,
											  state, sortKey, compare_datum_typed,
											  pivotDatum, pivotIsNull, pivotFullDatum);
			if (dist > 0)
				break;
			if (dist == 0)
			{
				mkqs_swap(bounds->lessEnd, bounds->lessStart, x);
				bounds->lessStart++;
			}
			bounds->lessEnd++;
		}

		while (bounds->lessEnd <= bounds->greaterStart)
		{
			dist = mkqs_compare_heap_to_pivot(x + bounds->greaterStart, depth,
											  state, sortKey, compare_datum_typed,
											  pivotDatum, pivotIsNull, pivotFullDatum);
			if (dist < 0)
				break;
			if (dist == 0)
			{
				mkqs_swap(bounds->greaterStart, bounds->greaterEnd, x);
				bounds->greaterEnd--;
			}
			bounds->greaterStart--;
		}

		if (bounds->lessEnd > bounds->greaterStart)
			return pivotIsNull;
		mkqs_swap(bounds->lessEnd, bounds->greaterStart, x);
		bounds->lessEnd++;
		bounds->greaterStart--;
	}
}

static bool
mkqs_partition_index_btree(SortTuple *x, size_t n, int depth,
						   Tuplesortstate *state,
						   MkqsCompareDatumTyped compare_datum_typed,
						   MkqsPartitionBounds *bounds)
{
	SortSupport sortKey = &state->base.sortKeys[depth];
	Datum		pivotDatum;
	Datum		pivotFullDatum = (Datum) 0;
	bool		pivotIsNull;
	int32		dist;

	if (depth == 0)
	{
		pivotDatum = x->datum1;
		pivotIsNull = x->isnull1;
		if (sortKey->abbrev_converter && !pivotIsNull)
		{
			bool		isNull;

			pivotFullDatum = mkqs_get_index_datum(x, sortKey, state, &isNull);
			Assert(!isNull);
		}
	}
	else
		pivotDatum = mkqs_get_index_datum(x, sortKey, state, &pivotIsNull);

	bounds->lessStart = 1;
	bounds->lessEnd = 1;
	bounds->greaterStart = n - 1;
	bounds->greaterEnd = n - 1;

	while (true)
	{
		CHECK_FOR_INTERRUPTS();

		while (bounds->lessEnd <= bounds->greaterStart)
		{
			dist = mkqs_compare_index_btree_to_pivot(x + bounds->lessEnd, depth,
													 state, sortKey, compare_datum_typed,
													 pivotDatum, pivotIsNull, pivotFullDatum);
			if (dist > 0)
				break;
			if (dist == 0)
			{
				mkqs_swap(bounds->lessEnd, bounds->lessStart, x);
				bounds->lessStart++;
			}
			bounds->lessEnd++;
		}

		while (bounds->lessEnd <= bounds->greaterStart)
		{
			dist = mkqs_compare_index_btree_to_pivot(x + bounds->greaterStart, depth,
													 state, sortKey, compare_datum_typed,
													 pivotDatum, pivotIsNull, pivotFullDatum);
			if (dist < 0)
				break;
			if (dist == 0)
			{
				mkqs_swap(bounds->greaterStart, bounds->greaterEnd, x);
				bounds->greaterEnd--;
			}
			bounds->greaterStart--;
		}

		if (bounds->lessEnd > bounds->greaterStart)
			return pivotIsNull;
		mkqs_swap(bounds->lessEnd, bounds->greaterStart, x);
		bounds->lessEnd++;
		bounds->greaterStart--;
	}
}

static pg_attribute_always_inline int
mkqs_compare_tuple_range(SortTuple *a, SortTuple *b,
						 int start_depth, int max_depth,
						 Tuplesortstate *state,
						 MkqsCompareTuple compare_tuple)
{
	for (int depth = start_depth; depth <= max_depth; depth++)
	{
		SortSupport sortKey = &state->base.sortKeys[depth];
		int			compare;

		compare = compare_tuple(a, b, depth, state, sortKey->comparator);
		if (compare != 0)
			return compare;
	}

	return 0;
}

/*
 * Check whether the tuples are nondecreasing over the complete ordering.
 * Equality is safe because every depth that can affect the final order is
 * included.
 */
static bool
mkqs_full_order_presorted_callbacks(SortTuple *x, size_t n,
									Tuplesortstate *state,
									MkqsCompareTuple compare_tuple)
{
	Assert(state->base.nKeys > 0);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		for (int depth = 0; depth < state->base.nKeys; depth++)
		{
			SortSupport sortKey = &state->base.sortKeys[depth];
			int			compare;

			compare = compare_tuple(x + i - 1, x + i, depth, state,
									sortKey->comparator);
			if (compare < 0)
				break;
			if (compare > 0)
				return false;
		}
	}

	return true;
}

/* Public precheck used before the mksort callbacks have been selected. */
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
							   Tuplesortstate *state,
							   MkqsCompareTuple compare_tuple)
{
	SortSupport sortKey = &state->base.sortKeys[depth];

	Assert(depth >= 0);
	Assert(depth < state->base.nKeys);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		if (compare_tuple(x + i - 1, x + i, depth, state,
						  sortKey->comparator) >= 0)
			return false;
	}

	return true;
}

/* Find the median of three values */
static pg_noinline int
get_median_from_three(int a,
					  int b,
					  int c,
					  SortTuple *x,
					  int depth,
					  Tuplesortstate *state,
					  MkqsCompareTuple compare_tuple)
{
	SortSupport sortKey = &state->base.sortKeys[depth];
	MkqsCompareDatumTyped compare_datum_typed = sortKey->comparator;

	return compare_tuple(x + a, x + b, depth, state,
						 compare_datum_typed) < 0 ?
		(compare_tuple(x + b, x + c, depth, state,
					   compare_datum_typed) < 0 ? b :
		 (compare_tuple(x + a, x + c, depth, state,
						compare_datum_typed) < 0 ? c : a)) :
		(compare_tuple(x + b, x + c, depth, state,
					   compare_datum_typed) > 0 ? b :
		 (compare_tuple(x + a, x + c, depth, state,
						compare_datum_typed) < 0 ? a : c));
}

/*
 * Major of multi-key quick sort
 *
 * seenNull indicates whether we have seen NULL in any datum we checked
 */
static void
mk_qsort_tuple_impl(SortTuple *x,
					size_t n,
					int depth,
					Tuplesortstate *state,
					bool seenNull,
					MkqsCompareTuple compare_tuple,
					MkqsPartition partition)
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
				m,
				l,
				r,
				d;
	int32		dist;
	bool		isDatumNull;
	MkqsPartitionBounds bounds;

	Assert(depth <= state->base.nKeys);
	Assert(state->base.sortKeys);
	if (n <= 1)
		return;

	/* If we have exceeded the max depth, return immediately */
	if (depth == state->base.nKeys)
		return;

	state->mkqsUsed = true;

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
											 state->base.nKeys - 1, state,
											 compare_tuple) <= 0)
					break;
				mkqs_swap(l, l - 1, x);
			}
		return;
	}

	if (depth == 0)
	{
		/* The caller may already have performed and failed this exact scan. */
		if (!state->mkqsTopPresortFailed &&
			mkqs_full_order_presorted_callbacks(x, n, state, compare_tuple))
			return;
	}
	else
	{
		/* For current depth, perform strictly increasing check */
		if (mkqs_depth_strictly_increasing(x, n, depth, state,
										   compare_tuple))
			return;
	}

	/* Select pivot by random and move it to the first position */
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

	isDatumNull = partition(x, n, depth, state,
							state->base.sortKeys[depth].comparator, &bounds);

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
	mk_qsort_tuple_impl(x,
						dist,
						depth,
						state,
						seenNull,
						compare_tuple,
						partition);

	/* Recursively sort the equal part */

	/*
	 * (x + dist) means the first tuple in the equal part Since all tuples
	 * have equal datums at current depth, we just check any one of them to
	 * determine whether we have seen null datum.
	 */
	/* (lessStart + n - greaterEnd - 1) means the size of equal part */
	tupCount = lessStart + n - greaterEnd - 1;

	if (depth < state->base.nKeys - 1)
	{
		mk_qsort_tuple_impl(x + dist,
							tupCount,
							depth + 1,
							state,
							seenNull || isDatumNull,
							compare_tuple,
							partition);
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
	mk_qsort_tuple_impl(x + n - dist,
						dist,
						depth,
						state,
						seenNull,
						compare_tuple,
						partition);

}

static void
mk_qsort_tuple(SortTuple *x,
			   size_t n,
			   int depth,
			   Tuplesortstate *state,
			   bool seenNull)
{
	if (state->base.mkqsTupleType == MKQS_TUPLE_TYPE_HEAP)
		mk_qsort_tuple_impl(x, n, depth, state, seenNull,
							mkqs_compare_tuple_heap, mkqs_partition_heap);
	else
	{
		Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
		mk_qsort_tuple_impl(x, n, depth, state, seenNull,
							mkqs_compare_tuple_index_btree,
							mkqs_partition_index_btree);
	}
}

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
 * compare_datum_typed compares two non-NULL datums in the sort operator's
 * natural direction.  mkqs_compare_datum() adds NULL and reverse-order
 * semantics around it.
 *
 * compare_tuple and partition are selected once for the tuple representation
 * at the mk_qsort_tuple() entry point.  The caller supplies the comparator for
 * the current sort key so that these callbacks need only specialize datum
 * extraction and tuple layout.
 */
typedef int (*MkqsCompareDatumTyped) (Datum datum1, Datum datum2,
									  SortSupport sortKey);
typedef int (*MkqsCompareTuple) (SortTuple *a, SortTuple *b, int depth,
								 Tuplesortstate *state,
								 MkqsCompareDatumTyped compare_datum_typed);
typedef bool (*MkqsPartition) (SortTuple *x, size_t n, int depth,
							   Tuplesortstate *state,
							   MkqsCompareDatumTyped compare_datum_typed,
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

/* Compare two heap SortTuples at exactly one sort-key depth. */
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
		/* datum1 caches the leading key, possibly in abbreviated form. */
		compare = mkqs_compare_datum(a->datum1, a->isnull1,
									 b->datum1, b->isnull1,
									 sortKey, compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			a->isnull1 || b->isnull1)
			return compare;

		/* Equal abbreviations must be resolved using the full datums. */
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

/* Compare two btree index SortTuples at exactly one sort-key depth. */
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
		/* datum1 caches the leading key, possibly in abbreviated form. */
		compare = mkqs_compare_datum(a->datum1, a->isnull1,
									 b->datum1, b->isnull1,
									 sortKey, compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			a->isnull1 || b->isnull1)
			return compare;

		/* Equal abbreviations must be resolved using the full datums. */
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

/*
 * Compare one heap tuple with an already extracted pivot datum.  Keeping the
 * pivot outside the loop avoids extracting it for every partition comparison.
 */
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
		/* Both leading values are cached, and might be abbreviations. */
		compare = mkqs_compare_datum(tuple->datum1, tuple->isnull1,
									 pivotDatum, pivotIsNull,
									 sortKey, compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			tuple->isnull1 || pivotIsNull)
			return compare;

		/* Resolve an abbreviation collision without re-extracting the pivot. */
		datum = mkqs_get_heap_datum(tuple, sortKey, state, &isNull);
		Assert(!isNull);
		return mkqs_compare_datum(datum, false, pivotFullDatum, false,
								  sortKey, sortKey->abbrev_full_comparator);
	}

	datum = mkqs_get_heap_datum(tuple, sortKey, state, &isNull);
	return mkqs_compare_datum(datum, isNull, pivotDatum, pivotIsNull,
							  sortKey, compare_datum_typed);
}

/* Btree index variant of mkqs_compare_heap_to_pivot(). */
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
		/* Both leading values are cached, and might be abbreviations. */
		compare = mkqs_compare_datum(tuple->datum1, tuple->isnull1,
									 pivotDatum, pivotIsNull,
									 sortKey, compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			tuple->isnull1 || pivotIsNull)
			return compare;

		/* Resolve an abbreviation collision without re-extracting the pivot. */
		datum = mkqs_get_index_datum(tuple, sortKey, state, &isNull);
		Assert(!isNull);
		return mkqs_compare_datum(datum, false, pivotFullDatum, false,
								  sortKey, sortKey->abbrev_full_comparator);
	}

	datum = mkqs_get_index_datum(tuple, sortKey, state, &isNull);
	return mkqs_compare_datum(datum, isNull, pivotDatum, pivotIsNull,
							  sortKey, compare_datum_typed);
}

/*
 * Partition heap tuples around x[0], comparing only the current key depth.
 * Tuples equal at this depth accumulate at both ends; bounds describes all
 * four partition boundaries when the unprocessed range becomes empty.  Return
 * whether the pivot datum is NULL so recursion can propagate uniqueness
 * semantics.
 */
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

	/* Extract the pivot once before scanning the rest of the partition. */
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

		/* Scan from the left, moving equal values to the left edge. */
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

		/* Scan from the right, moving equal values to the right edge. */
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

/* Btree index variant of mkqs_partition_heap(). */
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

	/* Extract the pivot once before scanning the rest of the partition. */
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

		/* Scan from the left, moving equal values to the left edge. */
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

		/* Scan from the right, moving equal values to the right edge. */
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

/* Compare two tuples over the inclusive range of sort-key depths. */
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

/* Precheck used before the mksort tuple callbacks have been selected. */
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

/* Return the array index of the median tuple at the current depth. */
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
 * Recursively sort x at one key depth using three-way partitioning.
 *
 * compare_tuple and partition remain fixed for the tuple representation
 * throughout recursion.  Each comparison receives the current sort key's
 * typed comparator.  seenNull records whether any preceding equal key was
 * NULL, which the terminal duplicate handler needs for uniqueness checks.
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
	MkqsPartitionBounds bounds;

	Assert(depth <= state->base.nKeys);
	Assert(state->base.sortKeys);
	if (n <= 1)
		return;

	/* If we have reached the maximum depth, return immediately. */
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

	isDatumNull = partition(x, n, depth, state,
							state->base.sortKeys[depth].comparator, &bounds);

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
						seenNull,
						compare_tuple,
						partition);

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
							seenNull || isDatumNull,
							compare_tuple,
							partition);
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
						seenNull,
						compare_tuple,
						partition);

}

/*
 * Select tuple-representation callbacks once, outside the recursive hot path.
 */
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

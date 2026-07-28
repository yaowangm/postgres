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

typedef Datum (*MkqsGetDatumFunc) (SortTuple *tuple, SortSupport sortKey,
								   Tuplesortstate *state, bool *isNull);
typedef int (*MkqsCompareDatumFunc) (Datum datum1, bool isNull1,
									 Datum datum2, bool isNull2,
									 SortSupport sortKey);

typedef struct MkqsPivotCompareContext
{
	Datum		pivotDatum;
	bool		pivotIsNull;
	Datum		pivotFullDatum;
	SortSupport sortKey;
	Tuplesortstate *state;
	MkqsGetDatumFunc getdatum;
	MkqsCompareDatumFunc comparedatum;
	bool		useDatum1;
} MkqsPivotCompareContext;

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

/* Check whether the current tuple datum is NULL. */
static bool
mkqs_datum_is_null(SortTuple *tuple, int depth, Tuplesortstate *state,
				   MkqsGetDatumFunc getdatum)
{
	bool		isNull;

	Assert(depth < state->base.nKeys);

	if (depth == 0)
		return tuple->isnull1;

	(void) getdatum(tuple, &state->base.sortKeys[depth], state, &isNull);

	return isNull;
}

/* Apply a comparator not recognized as one of the simple datum comparators. */
static int
mkqs_compare_datum_generic(Datum datum1, bool isNull1,
						   Datum datum2, bool isNull2,
						   SortSupport sortKey)
{
	return ApplySortComparator(datum1, isNull1, datum2, isNull2, sortKey);
}

#if SIZEOF_DATUM >= 8
/* Compare signed 64-bit datums without an indirect SortSupport comparator. */
static int
mkqs_compare_datum_signed(Datum datum1, bool isNull1,
						  Datum datum2, bool isNull2,
						  SortSupport sortKey)
{
	int			compare;

	if (isNull1 || isNull2)
	{
		if (isNull1 && isNull2)
			return 0;
		return isNull1 == sortKey->ssup_nulls_first ? -1 : 1;
	}

	compare = (DatumGetInt64(datum1) > DatumGetInt64(datum2)) -
		(DatumGetInt64(datum1) < DatumGetInt64(datum2));
	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(compare);
	return compare;
}

/* Compare unsigned 64-bit datums without an indirect SortSupport comparator. */
static int
mkqs_compare_datum_unsigned(Datum datum1, bool isNull1,
							Datum datum2, bool isNull2,
							SortSupport sortKey)
{
	int			compare;

	if (isNull1 || isNull2)
	{
		if (isNull1 && isNull2)
			return 0;
		return isNull1 == sortKey->ssup_nulls_first ? -1 : 1;
	}

	compare = (DatumGetUInt64(datum1) > DatumGetUInt64(datum2)) -
		(DatumGetUInt64(datum1) < DatumGetUInt64(datum2));
	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(compare);
	return compare;
}
#endif

/* Compare signed 32-bit datums without an indirect SortSupport comparator. */
static int
mkqs_compare_datum_int32(Datum datum1, bool isNull1,
						 Datum datum2, bool isNull2,
						 SortSupport sortKey)
{
	int			compare;

	if (isNull1 || isNull2)
	{
		if (isNull1 && isNull2)
			return 0;
		return isNull1 == sortKey->ssup_nulls_first ? -1 : 1;
	}

	compare = (DatumGetInt32(datum1) > DatumGetInt32(datum2)) -
		(DatumGetInt32(datum1) < DatumGetInt32(datum2));
	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(compare);
	return compare;
}

/* Compare one tuple with the datum cached for the partition pivot. */
static pg_attribute_always_inline int
mkqs_compare_tuple_to_pivot(SortTuple *tuple,
							MkqsPivotCompareContext *context)
{
	Datum		datum;
	bool		isNull;
	int			compare;

	if (context->useDatum1)
	{
		datum = tuple->datum1;
		isNull = tuple->isnull1;
	}
	else
		datum = context->getdatum(tuple, context->sortKey,
								context->state, &isNull);

	compare = context->comparedatum(datum, isNull,
								   context->pivotDatum,
								   context->pivotIsNull,
								   context->sortKey);
	if (compare != 0 || !context->sortKey->abbrev_converter ||
		isNull || context->pivotIsNull)
		return compare;

	datum = context->getdatum(tuple, context->sortKey,
								context->state, &isNull);
	Assert(!isNull);
	compare = context->sortKey->abbrev_full_comparator(datum,
													 context->pivotFullDatum,
													 context->sortKey);
	if (context->sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(compare);
	return compare;
}

/* Partition around x[0], comparing only the current key depth. */
static void
mkqs_partition(SortTuple *x, size_t n, MkqsPartitionBounds *bounds,
			   MkqsPivotCompareContext *context)
{
	int32		dist;

	bounds->lessStart = 1;
	bounds->lessEnd = 1;
	bounds->greaterStart = n - 1;
	bounds->greaterEnd = n - 1;

	while (true)
	{
		CHECK_FOR_INTERRUPTS();

		while (bounds->lessEnd <= bounds->greaterStart)
		{
			dist = mkqs_compare_tuple_to_pivot(x + bounds->lessEnd, context);
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
			dist = mkqs_compare_tuple_to_pivot(x + bounds->greaterStart,
												 context);
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
			return;
		mkqs_swap(bounds->lessEnd, bounds->greaterStart, x);
		bounds->lessEnd++;
		bounds->greaterStart--;
	}
}

/* Compare an inclusive range of tuple sort-key depths. */
static pg_attribute_always_inline int
mkqs_compare_tuples(SortTuple *a, SortTuple *b,
					int start_depth, int max_depth,
					Tuplesortstate *state,
					MkqsGetDatumFunc getdatum,
					MkqsCompareDatumFunc *comparedatums)
{
	TuplesortPublic *base = &state->base;
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
		compare = comparedatums[0](a->datum1, a->isnull1,
											 b->datum1, b->isnull1,
											 sortKey);
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

	if (depth == 0)
	{
		SortSupport sortKey = &base->sortKeys[0];
		Datum		datum1;
		Datum		datum2;
		bool		isnull1;
		bool		isnull2;

		datum1 = getdatum(a, sortKey, state, &isnull1);
		datum2 = getdatum(b, sortKey, state, &isnull2);
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

		datum1 = getdatum(a, sortKey, state, &isnull1);
		datum2 = getdatum(b, sortKey, state, &isnull2);
		compare = comparedatums[depth](datum1, isnull1,
											 datum2, isnull2,
											 sortKey);
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
								MkqsGetDatumFunc getdatum,
								MkqsCompareDatumFunc *comparedatums)
{
	Assert(state->base.nKeys > 0);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		if (mkqs_compare_tuples(x + i - 1, x + i, 0,
								state->base.nKeys - 1, state,
								getdatum, comparedatums) > 0)
			return false;
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
							   MkqsGetDatumFunc getdatum,
							   MkqsCompareDatumFunc *comparedatums)
{
	Assert(depth >= 0);
	Assert(depth < state->base.nKeys);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		if (mkqs_compare_tuples(x + i - 1, x + i,
								depth, depth, state,
								getdatum, comparedatums) >= 0)
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
					  Tuplesortstate *state,
					  MkqsGetDatumFunc getdatum,
					  MkqsCompareDatumFunc *comparedatums)
{
	return mkqs_compare_tuples(x + a, x + b, depth, depth,
							   state, getdatum, comparedatums) < 0 ?
			 (mkqs_compare_tuples(x + b, x + c, depth, depth,
								  state, getdatum, comparedatums) < 0 ? b :
			  (mkqs_compare_tuples(x + a, x + c, depth, depth,
								   state, getdatum, comparedatums) < 0 ? c : a)) :
			 (mkqs_compare_tuples(x + b, x + c, depth, depth,
								  state, getdatum, comparedatums) > 0 ? b :
			  (mkqs_compare_tuples(x + a, x + c, depth, depth,
								   state, getdatum, comparedatums) < 0 ? a : c));
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
					MkqsGetDatumFunc getdatum,
					MkqsCompareDatumFunc *comparedatums)
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
	MkqsPivotCompareContext pivotContext;


	Assert(depth <= state->base.nKeys);
	Assert(state->base.sortKeys);
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
			mkqs_full_order_presorted_callbacks(x, n, state,
											getdatum, comparedatums))
			return;
	}
	else
	{
		/* For current depth, perform strictly increasing check */
		if (mkqs_depth_strictly_increasing(x, n, depth, state,
										   getdatum, comparedatums))
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
		for (m = 0; m < n; m++)
			for (l = m; l > 0; l--)
			{
				if (mkqs_compare_tuples(x + l - 1, x + l, depth,
										state->base.nKeys - 1, state,
										getdatum, comparedatums) <= 0)
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
		l = get_median_from_three(l, l + d, l + 2 * d, x, depth,
								  state, getdatum, comparedatums);
		m = get_median_from_three(m - d, m, m + d, x, depth,
								  state, getdatum, comparedatums);
		r = get_median_from_three(r - 2 * d, r - d, r, x, depth,
								  state, getdatum, comparedatums);
	}
	lessStart = get_median_from_three(l, m, r, x, depth, state,
									  getdatum, comparedatums);
	mkqs_swap(0, lessStart, x);

	pivotContext.sortKey = &state->base.sortKeys[depth];
	pivotContext.state = state;
	pivotContext.getdatum = getdatum;
	pivotContext.comparedatum = comparedatums[depth];
	pivotContext.useDatum1 = depth == 0;
	pivotContext.pivotFullDatum = (Datum) 0;
	if (depth == 0)
	{
		pivotContext.pivotDatum = x->datum1;
		pivotContext.pivotIsNull = x->isnull1;
		if (pivotContext.sortKey->abbrev_converter &&
			!pivotContext.pivotIsNull)
		{
			bool		isNull;

			pivotContext.pivotFullDatum = getdatum(x,
														 pivotContext.sortKey,
														 state, &isNull);
			Assert(!isNull);
		}
	}
	else
		pivotContext.pivotDatum = getdatum(x,
												 pivotContext.sortKey,
												 state,
												 &pivotContext.pivotIsNull);
	mkqs_partition(x, n, &bounds, &pivotContext);

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
						getdatum,
						comparedatums);

	/* Recursively sort the equal part */

	/*
	 * (x + dist) means the first tuple in the equal part Since all tuples
	 * have equal datums at current depth, we just check any one of them to
	 * determine whether we have seen null datum.
	 */
	isDatumNull = mkqs_datum_is_null(x + dist, depth, state, getdatum);

	/* (lessStart + n - greaterEnd - 1) means the size of equal part */
	tupCount = lessStart + n - greaterEnd - 1;

	if (depth < state->base.nKeys - 1)
	{
		mk_qsort_tuple_impl(x + dist,
							tupCount,
							depth + 1,
							state,
							seenNull || isDatumNull,
							getdatum,
							comparedatums);
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
						getdatum,
						comparedatums);

}

/* Select tuple-representation callbacks once, before entering recursion. */
static void
mk_qsort_tuple(SortTuple *x,
			   size_t n,
			   int depth,
			   Tuplesortstate *state,
			   bool seenNull)
{
	MkqsCompareDatumFunc *comparedatums;

	comparedatums = palloc(sizeof(*comparedatums) *
		state->base.nKeys);
	for (int keyno = 0; keyno < state->base.nKeys; keyno++)
	{
		SortSupport sortKey = &state->base.sortKeys[keyno];

#if SIZEOF_DATUM >= 8
		if (sortKey->comparator == ssup_datum_signed_cmp)
			comparedatums[keyno] = mkqs_compare_datum_signed;
		else if (sortKey->comparator == ssup_datum_unsigned_cmp)
			comparedatums[keyno] = mkqs_compare_datum_unsigned;
		else
#endif
		if (sortKey->comparator == ssup_datum_int32_cmp)
			comparedatums[keyno] = mkqs_compare_datum_int32;
		else
			comparedatums[keyno] = mkqs_compare_datum_generic;
	}

	if (state->base.mkqsTupleType == MKQS_TUPLE_TYPE_HEAP)
		mk_qsort_tuple_impl(x, n, depth, state, seenNull,
							mkqs_get_heap_datum, comparedatums);
	else
	{
		Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
		mk_qsort_tuple_impl(x, n, depth, state, seenNull,
							mkqs_get_index_datum, comparedatums);
	}
	pfree(comparedatums);
}

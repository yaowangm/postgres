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

typedef int (*MkqsCompareKeyFunc) (SortTuple *a, SortTuple *b,
								   SortSupport sortKey,
								   Tuplesortstate *state);
typedef Datum (*MkqsGetDatumFunc) (SortTuple *tuple, SortSupport sortKey,
								   Tuplesortstate *state, bool *isNull);
typedef struct MkqsContext MkqsContext;
typedef int (*MkqsComparePivotFunc) (SortTuple *tuple,
									 MkqsContext *context);

typedef struct MkqsKeyCallbacks
{
	/* Both callbacks include tuple access and datum comparison. */
	MkqsCompareKeyFunc compare_tuple;
	MkqsComparePivotFunc compare_to_pivot;
} MkqsKeyCallbacks;

struct MkqsContext
{
	Tuplesortstate *state;
	MkqsGetDatumFunc get_datum;
	MkqsKeyCallbacks *keys;
	SortSupport sortKey;
	Datum		pivotDatum;
	Datum		pivotFullDatum;
	bool		pivotIsNull;
};

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

#if SIZEOF_DATUM >= 8
/* Inline scalar comparators used inside the coarse-grained callbacks. */
static pg_attribute_always_inline int
mkqs_compare_signed_datums(Datum datum1, bool isNull1,
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

static pg_attribute_always_inline int
mkqs_compare_unsigned_datums(Datum datum1, bool isNull1,
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

static pg_attribute_always_inline int
mkqs_compare_int32_datums(Datum datum1, bool isNull1,
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

/* Fetch both full datums for one key, using datum1 for the leading key. */
static pg_attribute_always_inline void
mkqs_get_heap_key_datums(SortTuple *a, SortTuple *b, SortSupport sortKey,
						 Tuplesortstate *state,
						 Datum *datum1, bool *isNull1,
						 Datum *datum2, bool *isNull2)
{
	if (sortKey == state->base.sortKeys)
	{
		*datum1 = a->datum1;
		*isNull1 = a->isnull1;
		*datum2 = b->datum1;
		*isNull2 = b->isnull1;
		return;
	}

	*datum1 = mkqs_get_heap_datum(a, sortKey, state, isNull1);
	*datum2 = mkqs_get_heap_datum(b, sortKey, state, isNull2);
}

static pg_attribute_always_inline void
mkqs_get_index_key_datums(SortTuple *a, SortTuple *b, SortSupport sortKey,
						  Tuplesortstate *state,
						  Datum *datum1, bool *isNull1,
						  Datum *datum2, bool *isNull2)
{
	if (sortKey == state->base.sortKeys)
	{
		*datum1 = a->datum1;
		*isNull1 = a->isnull1;
		*datum2 = b->datum1;
		*isNull2 = b->isnull1;
		return;
	}

	*datum1 = mkqs_get_index_datum(a, sortKey, state, isNull1);
	*datum2 = mkqs_get_index_datum(b, sortKey, state, isNull2);
}

/* Generic exact-key callbacks, including abbreviated-key resolution. */
static int
mkqs_compare_heap_key(SortTuple *a, SortTuple *b, SortSupport sortKey,
					  Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;
	int			compare;

	if (sortKey == state->base.sortKeys)
	{
		compare = ApplySortComparator(a->datum1, a->isnull1,
									  b->datum1, b->isnull1, sortKey);
		if (compare != 0 || !sortKey->abbrev_converter ||
			a->isnull1 || b->isnull1)
			return compare;

		datum1 = mkqs_get_heap_datum(a, sortKey, state, &isNull1);
		datum2 = mkqs_get_heap_datum(b, sortKey, state, &isNull2);
		Assert(!isNull1 && !isNull2);
		compare = sortKey->abbrev_full_comparator(datum1, datum2, sortKey);
		if (sortKey->ssup_reverse)
			INVERT_COMPARE_RESULT(compare);
		return compare;
	}

	mkqs_get_heap_key_datums(a, b, sortKey, state,
							 &datum1, &isNull1, &datum2, &isNull2);
	return ApplySortComparator(datum1, isNull1, datum2, isNull2, sortKey);
}

static int
mkqs_compare_index_key(SortTuple *a, SortTuple *b, SortSupport sortKey,
					   Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;
	int			compare;

	if (sortKey == state->base.sortKeys)
	{
		compare = ApplySortComparator(a->datum1, a->isnull1,
									  b->datum1, b->isnull1, sortKey);
		if (compare != 0 || !sortKey->abbrev_converter ||
			a->isnull1 || b->isnull1)
			return compare;

		datum1 = mkqs_get_index_datum(a, sortKey, state, &isNull1);
		datum2 = mkqs_get_index_datum(b, sortKey, state, &isNull2);
		Assert(!isNull1 && !isNull2);
		compare = sortKey->abbrev_full_comparator(datum1, datum2, sortKey);
		if (sortKey->ssup_reverse)
			INVERT_COMPARE_RESULT(compare);
		return compare;
	}

	mkqs_get_index_key_datums(a, b, sortKey, state,
							  &datum1, &isNull1, &datum2, &isNull2);
	return ApplySortComparator(datum1, isNull1, datum2, isNull2, sortKey);
}

#if SIZEOF_DATUM >= 8
/* Scalar exact-key callbacks keep accessor and comparison in one call. */
static int
mkqs_compare_heap_signed_key(SortTuple *a, SortTuple *b,
							 SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;

	mkqs_get_heap_key_datums(a, b, sortKey, state,
							 &datum1, &isNull1, &datum2, &isNull2);
	return mkqs_compare_signed_datums(datum1, isNull1, datum2, isNull2,
									  sortKey);
}

static int
mkqs_compare_heap_unsigned_key(SortTuple *a, SortTuple *b,
							   SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;

	mkqs_get_heap_key_datums(a, b, sortKey, state,
							 &datum1, &isNull1, &datum2, &isNull2);
	return mkqs_compare_unsigned_datums(datum1, isNull1, datum2, isNull2,
										sortKey);
}

static int
mkqs_compare_index_signed_key(SortTuple *a, SortTuple *b,
							  SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;

	mkqs_get_index_key_datums(a, b, sortKey, state,
							  &datum1, &isNull1, &datum2, &isNull2);
	return mkqs_compare_signed_datums(datum1, isNull1, datum2, isNull2,
									  sortKey);
}

static int
mkqs_compare_index_unsigned_key(SortTuple *a, SortTuple *b,
								SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;

	mkqs_get_index_key_datums(a, b, sortKey, state,
							  &datum1, &isNull1, &datum2, &isNull2);
	return mkqs_compare_unsigned_datums(datum1, isNull1, datum2, isNull2,
										sortKey);
}
#endif

/* 32-bit scalar exact-key callbacks. */
static int
mkqs_compare_heap_int32_key(SortTuple *a, SortTuple *b,
							SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;

	mkqs_get_heap_key_datums(a, b, sortKey, state,
							 &datum1, &isNull1, &datum2, &isNull2);
	return mkqs_compare_int32_datums(datum1, isNull1, datum2, isNull2,
									 sortKey);
}

static int
mkqs_compare_index_int32_key(SortTuple *a, SortTuple *b,
							 SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;

	mkqs_get_index_key_datums(a, b, sortKey, state,
							  &datum1, &isNull1, &datum2, &isNull2);
	return mkqs_compare_int32_datums(datum1, isNull1, datum2, isNull2,
									 sortKey);
}

/* Cache the partition pivot once using the selected tuple representation. */
static void
mkqs_init_pivot(SortTuple *pivot, int depth, MkqsContext *context)
{
	Tuplesortstate *state = context->state;

	context->sortKey = &state->base.sortKeys[depth];
	context->pivotFullDatum = (Datum) 0;

	if (depth == 0)
	{
		context->pivotDatum = pivot->datum1;
		context->pivotIsNull = pivot->isnull1;
		if (context->sortKey->abbrev_converter && !pivot->isnull1)
		{
			bool		isNull;

			context->pivotFullDatum =
				context->get_datum(pivot, context->sortKey, state, &isNull);
			Assert(!isNull);
		}
	}
	else
		context->pivotDatum = context->get_datum(pivot, context->sortKey,
												 state, &context->pivotIsNull);
}

/* Generic leading-key pivot callbacks resolve abbreviation when necessary. */
static int
mkqs_compare_heap_leading_to_pivot(SortTuple *tuple,
								   MkqsContext *context)
{
	int			compare;

	compare = ApplySortComparator(tuple->datum1, tuple->isnull1,
								  context->pivotDatum,
								  context->pivotIsNull, context->sortKey);
	if (compare != 0 || !context->sortKey->abbrev_converter ||
		tuple->isnull1 || context->pivotIsNull)
		return compare;

	{
		Datum		datum;
		bool		isNull;

		datum = mkqs_get_heap_datum(tuple, context->sortKey,
									context->state, &isNull);
		Assert(!isNull);
		compare = context->sortKey->abbrev_full_comparator(datum,
														   context->pivotFullDatum,
														   context->sortKey);
		if (context->sortKey->ssup_reverse)
			INVERT_COMPARE_RESULT(compare);
	}
	return compare;
}

static int
mkqs_compare_index_leading_to_pivot(SortTuple *tuple,
									MkqsContext *context)
{
	int			compare;

	compare = ApplySortComparator(tuple->datum1, tuple->isnull1,
								  context->pivotDatum,
								  context->pivotIsNull, context->sortKey);
	if (compare != 0 || !context->sortKey->abbrev_converter ||
		tuple->isnull1 || context->pivotIsNull)
		return compare;

	{
		Datum		datum;
		bool		isNull;

		datum = mkqs_get_index_datum(tuple, context->sortKey,
									 context->state, &isNull);
		Assert(!isNull);
		compare = context->sortKey->abbrev_full_comparator(datum,
														   context->pivotFullDatum,
														   context->sortKey);
		if (context->sortKey->ssup_reverse)
			INVERT_COMPARE_RESULT(compare);
	}
	return compare;
}

static int
mkqs_compare_heap_datum_to_pivot(SortTuple *tuple,
								 MkqsContext *context)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_heap_datum(tuple, context->sortKey, context->state,
								&isNull);
	return ApplySortComparator(datum, isNull, context->pivotDatum,
							   context->pivotIsNull, context->sortKey);
}

static int
mkqs_compare_index_datum_to_pivot(SortTuple *tuple,
								  MkqsContext *context)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_index_datum(tuple, context->sortKey, context->state,
								 &isNull);
	return ApplySortComparator(datum, isNull, context->pivotDatum,
							   context->pivotIsNull, context->sortKey);
}

#if SIZEOF_DATUM >= 8
/* Scalar pivot callbacks combine datum access and direct comparison. */
static int
mkqs_compare_signed_leading_to_pivot(SortTuple *tuple,
									 MkqsContext *context)
{
	return mkqs_compare_signed_datums(tuple->datum1, tuple->isnull1,
									  context->pivotDatum, context->pivotIsNull,
									  context->sortKey);
}

static int
mkqs_compare_unsigned_leading_to_pivot(SortTuple *tuple,
									   MkqsContext *context)
{
	return mkqs_compare_unsigned_datums(tuple->datum1, tuple->isnull1,
										context->pivotDatum, context->pivotIsNull,
										context->sortKey);
}

static int
mkqs_compare_heap_signed_to_pivot(SortTuple *tuple,
								  MkqsContext *context)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_heap_datum(tuple, context->sortKey, context->state,
								&isNull);
	return mkqs_compare_signed_datums(datum, isNull, context->pivotDatum,
									  context->pivotIsNull, context->sortKey);
}

static int
mkqs_compare_heap_unsigned_to_pivot(SortTuple *tuple,
									MkqsContext *context)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_heap_datum(tuple, context->sortKey, context->state,
								&isNull);
	return mkqs_compare_unsigned_datums(datum, isNull, context->pivotDatum,
										context->pivotIsNull, context->sortKey);
}

static int
mkqs_compare_index_signed_to_pivot(SortTuple *tuple,
								   MkqsContext *context)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_index_datum(tuple, context->sortKey, context->state,
								 &isNull);
	return mkqs_compare_signed_datums(datum, isNull, context->pivotDatum,
									  context->pivotIsNull, context->sortKey);
}

static int
mkqs_compare_index_unsigned_to_pivot(SortTuple *tuple,
									 MkqsContext *context)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_index_datum(tuple, context->sortKey, context->state,
								 &isNull);
	return mkqs_compare_unsigned_datums(datum, isNull, context->pivotDatum,
										context->pivotIsNull, context->sortKey);
}
#endif

static int
mkqs_compare_int32_leading_to_pivot(SortTuple *tuple,
									MkqsContext *context)
{
	return mkqs_compare_int32_datums(tuple->datum1, tuple->isnull1,
									 context->pivotDatum, context->pivotIsNull,
									 context->sortKey);
}

static int
mkqs_compare_heap_int32_to_pivot(SortTuple *tuple,
								 MkqsContext *context)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_heap_datum(tuple, context->sortKey, context->state,
								&isNull);
	return mkqs_compare_int32_datums(datum, isNull, context->pivotDatum,
									 context->pivotIsNull, context->sortKey);
}

static int
mkqs_compare_index_int32_to_pivot(SortTuple *tuple,
								  MkqsContext *context)
{
	Datum		datum;
	bool		isNull;

	datum = mkqs_get_index_datum(tuple, context->sortKey, context->state,
								 &isNull);
	return mkqs_compare_int32_datums(datum, isNull, context->pivotDatum,
									 context->pivotIsNull, context->sortKey);
}

/* Partition around x[0], comparing only the current key depth. */
static void
mkqs_partition(SortTuple *x, size_t n, MkqsPartitionBounds *bounds,
			   MkqsComparePivotFunc compare,
			   MkqsContext *context)
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
			dist = compare(x + bounds->lessEnd, context);
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
			dist = compare(x + bounds->greaterStart, context);
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

static pg_attribute_always_inline int
mkqs_compare_tuple_range(SortTuple *a, SortTuple *b,
						 int start_depth, int max_depth,
						 Tuplesortstate *state,
						 MkqsContext *context)
{
	for (int depth = start_depth; depth <= max_depth; depth++)
	{
		int			compare;

		compare = context->keys[depth].compare_tuple(a, b,
													 &state->base.sortKeys[depth],
													 state);
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
									MkqsContext *context)
{
	Assert(state->base.nKeys > 0);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		for (int depth = 0; depth < state->base.nKeys; depth++)
		{
			int			compare;

			compare = context->keys[depth].compare_tuple(x + i - 1,
														 x + i,
														 &state->base.sortKeys[depth],
														 state);
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
							   MkqsCompareKeyFunc comparekey)
{
	Assert(depth >= 0);
	Assert(depth < state->base.nKeys);

	for (size_t i = 1; i < n; i++)
	{
		CHECK_FOR_INTERRUPTS();
		if (comparekey(x + i - 1, x + i, &state->base.sortKeys[depth],
					   state) >= 0)
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
					  MkqsCompareKeyFunc comparekey)
{
	SortSupport sortKey = &state->base.sortKeys[depth];

	return comparekey(x + a, x + b, sortKey, state) < 0 ?
		(comparekey(x + b, x + c, sortKey, state) < 0 ? b :
		 (comparekey(x + a, x + c, sortKey, state) < 0 ? c : a)) :
		(comparekey(x + b, x + c, sortKey, state) > 0 ? b :
		 (comparekey(x + a, x + c, sortKey, state) < 0 ? a : c));
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
					MkqsContext *context)
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
											 context) <= 0)
					break;
				mkqs_swap(l, l - 1, x);
			}
		return;
	}

	if (depth == 0)
	{
		/* The caller may already have performed and failed this exact scan. */
		if (!state->mkqsTopPresortFailed &&
			mkqs_full_order_presorted_callbacks(x, n, state, context))
			return;
	}
	else
	{
		/* For current depth, perform strictly increasing check */
		if (mkqs_depth_strictly_increasing(x, n, depth, state,
										   context->keys[depth].compare_tuple))
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
								  state, context->keys[depth].compare_tuple);
		m = get_median_from_three(m - d, m, m + d, x, depth,
								  state, context->keys[depth].compare_tuple);
		r = get_median_from_three(r - 2 * d, r - d, r, x, depth,
								  state, context->keys[depth].compare_tuple);
	}
	lessStart = get_median_from_three(l, m, r, x, depth, state,
									  context->keys[depth].compare_tuple);
	mkqs_swap(0, lessStart, x);

	mkqs_init_pivot(x, depth, context);
	mkqs_partition(x, n, &bounds, context->keys[depth].compare_to_pivot,
				   context);
	isDatumNull = context->pivotIsNull;

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
						context);

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
							context);
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
						context);

}

/* Select representation- and type-specific callbacks once per top-level sort. */
static void
mkqs_init_context(Tuplesortstate *state, MkqsContext *context)
{
	bool		heapTuples;

	context->state = state;
	heapTuples = state->base.mkqsTupleType == MKQS_TUPLE_TYPE_HEAP;
	if (heapTuples)
		context->get_datum = mkqs_get_heap_datum;
	else
	{
		Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
		context->get_datum = mkqs_get_index_datum;
	}

	context->keys = palloc(sizeof(*context->keys) *
						   state->base.nKeys);
	for (int keyno = 0; keyno < state->base.nKeys; keyno++)
	{
		SortSupport sortKey = &state->base.sortKeys[keyno];

		/* Abbreviation requires the representation-specific full-datum path. */
		if (keyno == 0 && sortKey->abbrev_converter)
		{
			context->keys[keyno].compare_tuple = heapTuples ?
				mkqs_compare_heap_key : mkqs_compare_index_key;
			context->keys[keyno].compare_to_pivot = heapTuples ?
				mkqs_compare_heap_leading_to_pivot :
				mkqs_compare_index_leading_to_pivot;
		}
#if SIZEOF_DATUM >= 8
		else if (!sortKey->abbrev_converter &&
				 sortKey->comparator == ssup_datum_signed_cmp)
		{
			context->keys[keyno].compare_tuple = heapTuples ?
				mkqs_compare_heap_signed_key : mkqs_compare_index_signed_key;
			context->keys[keyno].compare_to_pivot = keyno == 0 ?
				mkqs_compare_signed_leading_to_pivot :
				(heapTuples ? mkqs_compare_heap_signed_to_pivot :
				 mkqs_compare_index_signed_to_pivot);
		}
		else if (!sortKey->abbrev_converter &&
				 sortKey->comparator == ssup_datum_unsigned_cmp)
		{
			context->keys[keyno].compare_tuple = heapTuples ?
				mkqs_compare_heap_unsigned_key : mkqs_compare_index_unsigned_key;
			context->keys[keyno].compare_to_pivot = keyno == 0 ?
				mkqs_compare_unsigned_leading_to_pivot :
				(heapTuples ? mkqs_compare_heap_unsigned_to_pivot :
				 mkqs_compare_index_unsigned_to_pivot);
		}
#endif
		else if (!sortKey->abbrev_converter &&
				 sortKey->comparator == ssup_datum_int32_cmp)
		{
			context->keys[keyno].compare_tuple = heapTuples ?
				mkqs_compare_heap_int32_key : mkqs_compare_index_int32_key;
			context->keys[keyno].compare_to_pivot = keyno == 0 ?
				mkqs_compare_int32_leading_to_pivot :
				(heapTuples ? mkqs_compare_heap_int32_to_pivot :
				 mkqs_compare_index_int32_to_pivot);
		}
		else
		{
			context->keys[keyno].compare_tuple = heapTuples ?
				mkqs_compare_heap_key : mkqs_compare_index_key;
			context->keys[keyno].compare_to_pivot = keyno == 0 ?
				(heapTuples ? mkqs_compare_heap_leading_to_pivot :
				 mkqs_compare_index_leading_to_pivot) :
				(heapTuples ? mkqs_compare_heap_datum_to_pivot :
				 mkqs_compare_index_datum_to_pivot);
		}
	}
}

static void
mkqs_destroy_context(MkqsContext *context)
{
	pfree(context->keys);
}

static void
mk_qsort_tuple(SortTuple *x,
			   size_t n,
			   int depth,
			   Tuplesortstate *state,
			   bool seenNull,
			   MkqsContext *context)
{
	Assert(context->state == state);

	mk_qsort_tuple_impl(x, n, depth, state, seenNull, context);
}

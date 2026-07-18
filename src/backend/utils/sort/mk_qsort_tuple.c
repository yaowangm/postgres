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

/* Swap two tuples in sort tuple array */
static inline void
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

static pg_attribute_always_inline void
mkqs_get_index_datum(const SortTuple *x1,
					 const SortTuple *x2,
					 int depth,
					 Tuplesortstate *state,
					 Datum *datum1,
					 bool *isNull1,
					 Datum *datum2,
					 bool *isNull2)
{
	TuplesortPublic *base = &state->base;

	Assert(base->mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
	Assert(base->mkqsGetDatumFunc != NULL);
	base->mkqsGetDatumFunc(x1, x2, depth, state,
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
		mkqs_get_index_datum(x, NULL, depth, state,
							 &datum, &isNull, NULL, NULL);

	return isNull;
}

static inline int
mkqs_apply_sort_comparator(Datum datum1,
						   bool isNull1,
						   Datum datum2,
						   bool isNull2,
						   SortSupport sortKey)
{
	int			ret;

	if (isNull1)
	{
		if (isNull2)
			return 0;
		else if (sortKey->ssup_nulls_first)
			return -1;
		else
			return 1;
	}
	else if (isNull2)
	{
		if (sortKey->ssup_nulls_first)
			return 1;
		else
			return -1;
	}

#if SIZEOF_DATUM >= 8
	if (sortKey->comparator == ssup_datum_signed_cmp)
	{
		int64		value1 = DatumGetInt64(datum1);
		int64		value2 = DatumGetInt64(datum2);

		ret = (value1 > value2) - (value1 < value2);
	}
	else if (sortKey->comparator == ssup_datum_unsigned_cmp)
	{
		uint64		value1 = DatumGetUInt64(datum1);
		uint64		value2 = DatumGetUInt64(datum2);

		ret = (value1 > value2) - (value1 < value2);
	}
	else
#endif
	if (sortKey->comparator == ssup_datum_int32_cmp)
	{
		int32		value1 = DatumGetInt32(datum1);
		int32		value2 = DatumGetInt32(datum2);

		ret = (value1 > value2) - (value1 < value2);
	}
	else
		return ApplySortComparator(datum1,
								   isNull1,
								   datum2,
								   isNull2,
								   sortKey);

	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(ret);

	return ret;
}

typedef enum MkqsPartitionCompareKind
{
	MKQS_PARTITION_COMPARE_GENERIC,
	MKQS_PARTITION_COMPARE_HEAP_GENERIC,
	MKQS_PARTITION_COMPARE_HEAP_SIGNED,
	MKQS_PARTITION_COMPARE_HEAP_UNSIGNED,
	MKQS_PARTITION_COMPARE_HEAP_INT32,
} MkqsPartitionCompareKind;

static pg_attribute_always_inline void
mkqs_get_heap_datums(SortTuple *tuple1, SortTuple *tuple2,
					 SortSupport sortKey, Tuplesortstate *state,
					 Datum *datum1, bool *isNull1,
					 Datum *datum2, bool *isNull2)
{
	HeapTupleData ltup;
	HeapTupleData rtup;

	ltup.t_len = ((MinimalTuple) tuple1->tuple)->t_len + MINIMAL_TUPLE_OFFSET;
	ltup.t_data = (HeapTupleHeader) ((char *) tuple1->tuple -
		MINIMAL_TUPLE_OFFSET);
	rtup.t_len = ((MinimalTuple) tuple2->tuple)->t_len + MINIMAL_TUPLE_OFFSET;
	rtup.t_data = (HeapTupleHeader) ((char *) tuple2->tuple -
		MINIMAL_TUPLE_OFFSET);
	*datum1 = heap_getattr(&ltup, sortKey->ssup_attno,
						   (TupleDesc) state->base.arg, isNull1);
	*datum2 = heap_getattr(&rtup, sortKey->ssup_attno,
						   (TupleDesc) state->base.arg, isNull2);
}

static pg_attribute_always_inline bool
mkqs_compare_nulls(bool isNull1, bool isNull2, SortSupport sortKey,
				   int *compare)
{
	if (isNull1)
	{
		if (isNull2)
			*compare = 0;
		else if (sortKey->ssup_nulls_first)
			*compare = -1;
		else
			*compare = 1;
		return true;
	}
	else if (isNull2)
	{
		if (sortKey->ssup_nulls_first)
			*compare = 1;
		else
			*compare = -1;
		return true;
	}

	return false;
}

#define MKQS_DEFINE_HEAP_COMPARATOR(name, ctype, datum_getter) \
static pg_attribute_always_inline int \
name(SortTuple *tuple1, SortTuple *tuple2, \
	 SortSupport sortKey, Tuplesortstate *state) \
{ \
	Datum		datum1; \
	Datum		datum2; \
	bool		isNull1; \
	bool		isNull2; \
	int			compare; \
 \
	mkqs_get_heap_datums(tuple1, tuple2, sortKey, state, \
						 &datum1, &isNull1, &datum2, &isNull2); \
	if (!mkqs_compare_nulls(isNull1, isNull2, sortKey, &compare)) \
	{ \
		ctype		value1 = datum_getter(datum1); \
		ctype		value2 = datum_getter(datum2); \
 \
		compare = (value1 > value2) - (value1 < value2); \
		if (sortKey->ssup_reverse) \
			INVERT_COMPARE_RESULT(compare); \
	} \
 \
	return compare; \
}

#if SIZEOF_DATUM >= 8
MKQS_DEFINE_HEAP_COMPARATOR(mkqs_compare_heap_signed, int64, DatumGetInt64)
MKQS_DEFINE_HEAP_COMPARATOR(mkqs_compare_heap_unsigned, uint64, DatumGetUInt64)
#endif
MKQS_DEFINE_HEAP_COMPARATOR(mkqs_compare_heap_int32, int32, DatumGetInt32)

#undef MKQS_DEFINE_HEAP_COMPARATOR

static pg_attribute_always_inline int
mkqs_compare_heap_generic(SortTuple *tuple1, SortTuple *tuple2,
						  SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;

	mkqs_get_heap_datums(tuple1, tuple2, sortKey, state,
						 &datum1, &isNull1, &datum2, &isNull2);

	return ApplySortComparator(datum1, isNull1,
							   datum2, isNull2,
							   sortKey);
}

static inline MkqsPartitionCompareKind
mkqs_select_partition_compare_kind(Tuplesortstate *state, int depth)
{
	SortSupport sortKey;

	if (state->base.mkqsTupleType != MKQS_TUPLE_TYPE_HEAP || depth == 0)
		return MKQS_PARTITION_COMPARE_GENERIC;

	sortKey = &state->base.sortKeys[depth];
#if SIZEOF_DATUM >= 8
	if (sortKey->comparator == ssup_datum_signed_cmp)
		return MKQS_PARTITION_COMPARE_HEAP_SIGNED;
	if (sortKey->comparator == ssup_datum_unsigned_cmp)
		return MKQS_PARTITION_COMPARE_HEAP_UNSIGNED;
#endif
	if (sortKey->comparator == ssup_datum_int32_cmp)
		return MKQS_PARTITION_COMPARE_HEAP_INT32;

	return MKQS_PARTITION_COMPARE_HEAP_GENERIC;
}

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

#define MKQS_PARTITION_LOOP(compare_left, compare_right) \
	do { \
		while (true) \
		{ \
			CHECK_FOR_INTERRUPTS(); \
 \
			while (bounds->lessEnd <= bounds->greaterStart) \
			{ \
				dist = (compare_left); \
				if (dist > 0) \
					break; \
				if (dist == 0) \
				{ \
					mkqs_swap(bounds->lessEnd, bounds->lessStart, x); \
					bounds->lessStart++; \
				} \
				bounds->lessEnd++; \
			} \
 \
			while (bounds->lessEnd <= bounds->greaterStart) \
			{ \
				dist = (compare_right); \
				if (dist < 0) \
					break; \
				if (dist == 0) \
				{ \
					mkqs_swap(bounds->greaterStart, bounds->greaterEnd, x); \
					bounds->greaterEnd--; \
				} \
				bounds->greaterStart--; \
			} \
 \
			if (bounds->lessEnd > bounds->greaterStart) \
				return; \
			mkqs_swap(bounds->lessEnd, bounds->greaterStart, x); \
			bounds->lessEnd++; \
			bounds->greaterStart--; \
		} \
	} while (0)

/*
 * Keep the generic comparator in the caller's code path.  Unlike the typed
 * cases, it does not benefit from dispatching to a specialized partition.
 */
static pg_attribute_always_inline void
mkqs_partition_generic(SortTuple *x, size_t n, int depth,
					   Tuplesortstate *state, MkqsPartitionBounds *bounds)
{
	SortTuple  *pivot = x;
	int32		dist;

	bounds->lessStart = 1;
	bounds->lessEnd = 1;
	bounds->greaterStart = n - 1;
	bounds->greaterEnd = n - 1;

	MKQS_PARTITION_LOOP(
		comparetup_mk(x + bounds->lessEnd, pivot,
					  depth, depth, state),
		comparetup_mk(x + bounds->greaterStart, pivot,
					  depth, depth, state));
	pg_unreachable();
}

/*
 * Heap generic comparators need neither tuple-representation dispatch nor
 * integer comparator detection once recursion has selected this depth.
 */
static pg_attribute_always_inline void
mkqs_partition_heap_generic(SortTuple *x, size_t n, int depth,
							Tuplesortstate *state,
							MkqsPartitionBounds *bounds)
{
	SortTuple  *pivot = x;
	SortSupport sortKey = &state->base.sortKeys[depth];
	int32		dist;

	bounds->lessStart = 1;
	bounds->lessEnd = 1;
	bounds->greaterStart = n - 1;
	bounds->greaterEnd = n - 1;

	MKQS_PARTITION_LOOP(
		mkqs_compare_heap_generic(x + bounds->lessEnd,
								  pivot, sortKey, state),
		mkqs_compare_heap_generic(x + bounds->greaterStart,
								  pivot, sortKey, state));
	pg_unreachable();
}

/*
 * Split one partition using a comparison path selected by the caller.  The
 * specialized cases keep tuple access and integer comparison decisions out
 * of the inner loops; the generic case retains the complete comparator.
 */
static pg_noinline void
mkqs_partition(SortTuple *x, size_t n, int depth, Tuplesortstate *state,
			   MkqsPartitionCompareKind compareKind,
			   MkqsPartitionBounds *bounds)
{
	SortTuple  *pivot = x;
	SortSupport sortKey = &state->base.sortKeys[depth];
	int32		dist;

	bounds->lessStart = 1;
	bounds->lessEnd = 1;
	bounds->greaterStart = n - 1;
	bounds->greaterEnd = n - 1;

	switch (compareKind)
	{
		case MKQS_PARTITION_COMPARE_GENERIC:
			pg_unreachable();

		case MKQS_PARTITION_COMPARE_HEAP_GENERIC:
			pg_unreachable();

#if SIZEOF_DATUM >= 8
		case MKQS_PARTITION_COMPARE_HEAP_SIGNED:
			MKQS_PARTITION_LOOP(
				mkqs_compare_heap_signed(x + bounds->lessEnd,
									 pivot, sortKey, state),
				mkqs_compare_heap_signed(x + bounds->greaterStart,
									 pivot, sortKey, state));
			pg_unreachable();

		case MKQS_PARTITION_COMPARE_HEAP_UNSIGNED:
			MKQS_PARTITION_LOOP(
				mkqs_compare_heap_unsigned(x + bounds->lessEnd,
									   pivot, sortKey, state),
				mkqs_compare_heap_unsigned(x + bounds->greaterStart,
									   pivot, sortKey, state));
			pg_unreachable();
#endif

		case MKQS_PARTITION_COMPARE_HEAP_INT32:
			MKQS_PARTITION_LOOP(
				mkqs_compare_heap_int32(x + bounds->lessEnd,
									pivot, sortKey, state),
				mkqs_compare_heap_int32(x + bounds->greaterStart,
									pivot, sortKey, state));
			pg_unreachable();

	}

	pg_unreachable();
}

#undef MKQS_PARTITION_LOOP

/*
 * Compare two tuples at specified depth
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
static inline int
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
	mkqs_get_index_datum(tuple1, tuple2, depth, state,
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
		ret = mkqs_apply_sort_comparator(datum1,
									  isNull1,
									  datum2,
									  isNull2,
									  sortKey);

	}

	return ret;
}

/*
 * Compare two tuples at first depth by some shortcuts
 *
 * The reason to use MkqsCompFuncType but not compare function pointers
 * directly is just for performance.
 */
static inline int
mkqs_compare_datum_by_shortcut(SortTuple      *tuple1,
							   SortTuple      *tuple2,
							   Tuplesortstate *state)
{
	int			ret;
	MkqsCompFuncType compFuncType = state->base.mkqsCompFuncType;
	SortSupport sortKey = &state->base.sortKeys[0];

	if (tuple1->isnull1)
	{
		if (tuple2->isnull1)
			return 0;
		else if (sortKey->ssup_nulls_first)
			return -1;
		else
			return 1;
	}
	else if (tuple2->isnull1)
	{
		if (sortKey->ssup_nulls_first)
			return 1;
		else
			return -1;
	}
#if SIZEOF_DATUM >= 8
	else if (compFuncType == MKQS_COMP_FUNC_SIGNED)
	{
		int64		datum1 = DatumGetInt64(tuple1->datum1);
		int64		datum2 = DatumGetInt64(tuple2->datum1);

		ret = (datum1 > datum2) - (datum1 < datum2);
	}
#endif
	else if (compFuncType == MKQS_COMP_FUNC_INT32)
	{
		int32		datum1 = DatumGetInt32(tuple1->datum1);
		int32		datum2 = DatumGetInt32(tuple2->datum1);

		ret = (datum1 > datum2) - (datum1 < datum2);
	}
	else
	{
		Assert(compFuncType == MKQS_COMP_FUNC_GENERIC);
		return ApplySortComparator(tuple1->datum1,
								   tuple1->isnull1,
								   tuple2->datum1,
								   tuple2->isnull1,
								   sortKey);
	}

	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(ret);

	return ret;
}

static int
comparetup_mk_heap_range(SortTuple *a, SortTuple *b,
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

		compare = mkqs_compare_datum_by_shortcut(a, b, state);
		if (compare != 0)
			return compare;

		if (!sortKey->abbrev_converter)
		{
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

		datum1 = heap_getattr(&ltup, sortKey->ssup_attno, tupDesc, &isnull1);
		datum2 = heap_getattr(&rtup, sortKey->ssup_attno, tupDesc, &isnull2);
		compare = ApplySortAbbrevFullComparator(datum1, isnull1,
										 datum2, isnull2, sortKey);
		if (compare != 0 || max_depth == 0)
			return compare;
		depth = 1;
	}

	if (depth == max_depth)
	{
		SortSupport sortKey = &base->sortKeys[depth];
		Datum		datum1;
		Datum		datum2;
		bool		isnull1;
		bool		isnull2;

		datum1 = heap_getattr(&ltup, sortKey->ssup_attno, tupDesc, &isnull1);
		datum2 = heap_getattr(&rtup, sortKey->ssup_attno, tupDesc, &isnull2);
		return mkqs_apply_sort_comparator(datum1, isnull1,
										  datum2, isnull2, sortKey);
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
		compare = mkqs_apply_sort_comparator(datum1, isnull1,
										 datum2, isnull2, sortKey);
		if (compare != 0)
			return compare;
	}

	return 0;
}

/* Compare heap tuples at exactly one sort-key depth. */
static pg_attribute_always_inline int
comparetup_mk_heap_single(SortTuple *a, SortTuple *b,
						 int depth, Tuplesortstate *state)
{
	TuplesortPublic *base = &state->base;
	SortSupport sortKey = &base->sortKeys[depth];
	HeapTupleData ltup;
	HeapTupleData rtup;
	Datum		datum1;
	Datum		datum2;
	bool		isnull1;
	bool		isnull2;
	int32		compare;

	Assert(depth >= 0);
	Assert(depth < base->nKeys);

	if (depth == 0)
	{
		compare = mkqs_compare_datum_by_shortcut(a, b, state);
		if (compare != 0 || !sortKey->abbrev_converter)
			return compare;
	}

	ltup.t_len = ((MinimalTuple) a->tuple)->t_len + MINIMAL_TUPLE_OFFSET;
	ltup.t_data = (HeapTupleHeader) ((char *) a->tuple - MINIMAL_TUPLE_OFFSET);
	rtup.t_len = ((MinimalTuple) b->tuple)->t_len + MINIMAL_TUPLE_OFFSET;
	rtup.t_data = (HeapTupleHeader) ((char *) b->tuple - MINIMAL_TUPLE_OFFSET);
	datum1 = heap_getattr(&ltup, sortKey->ssup_attno,
						  (TupleDesc) base->arg, &isnull1);
	datum2 = heap_getattr(&rtup, sortKey->ssup_attno,
						  (TupleDesc) base->arg, &isnull2);

	if (depth == 0)
		return ApplySortAbbrevFullComparator(datum1, isnull1,
										 datum2, isnull2, sortKey);

	return mkqs_apply_sort_comparator(datum1, isnull1,
								  datum2, isnull2, sortKey);
}

/* Compare an inclusive range of heap tuple sort-key depths. */
static pg_attribute_always_inline int
comparetup_mk_heap(SortTuple *a, SortTuple *b,
				   int start_depth, int max_depth,
				   Tuplesortstate *state)
{
	if (start_depth == max_depth)
		return comparetup_mk_heap_single(a, b, start_depth, state);

	return comparetup_mk_heap_range(a, b, start_depth, max_depth, state);
}

/* Compare an inclusive range of btree index tuple sort-key depths. */
static int
comparetup_mk_index_btree(SortTuple *a, SortTuple *b,
						 int start_depth, int max_depth,
						 Tuplesortstate *state)
{
	int			depth = start_depth;
	int			compare;

	Assert(state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE);
	Assert(start_depth >= 0);
	Assert(start_depth <= max_depth);
	Assert(max_depth < state->base.nKeys);

	if (depth == 0)
	{
		compare = mkqs_compare_datum_by_shortcut(a, b, state);

		if (compare != 0)
			return compare;

		if (!state->base.sortKeys->abbrev_converter)
		{
			if (max_depth == 0)
				return 0;
			depth = 1;
		}
	}

	for (; depth <= max_depth; depth++)
	{
		compare = comparetup_mk_index_btree_single(a, b, depth, state);
		if (compare != 0)
			return compare;
	}

	return 0;
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
 * included.
 *
 * comparetup_mk() does not yet expose btree's implicit heap TID depth, so use
 * the btree variant's full comparator until that depth is represented here.
 */
static bool
mkqs_full_order_presorted(SortTuple *x, size_t n, Tuplesortstate *state)
{
	Assert(state->base.nKeys > 0);

	for (size_t i = 1; i < n; i++)
	{
		int			compare;

		CHECK_FOR_INTERRUPTS();
		if (state->base.mkqsTupleType == MKQS_TUPLE_TYPE_INDEX_BTREE)
			compare = COMPARETUP(state, x + i - 1, x + i);
		else
			compare = comparetup_mk(x + i - 1, x + i, 0,
									 state->base.nKeys - 1, state);

		if (compare > 0)
			return false;
	}

	return true;
}

/*
 * Check only the current depth.  Equality is not sufficient to return from
 * mksort because later depths have not been checked; equal groups still need
 * to recurse to the next depth.
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
static inline int
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

#ifdef USE_ASSERT_CHECKING
/*
 * Verify whether the SortTuple list is ordered or not at specified depth
 */
static void
mkqs_verify(SortTuple *x,
			int n,
			int depth,
			Tuplesortstate *state)
{
	int			ret;

	for (int i = 0; i < n - 1; i++)
	{
		ret = comparetup_mk(x + i, x + i + 1,
							depth, depth, state);
		Assert(ret <= 0);
	}
}
#endif

static void mk_qsort_tuple(SortTuple *x,
						   size_t n,
						   int depth,
						   Tuplesortstate *state,
						   bool seenNull);

/*
 * If the leading key is already nondecreasing, avoid re-partitioning it.
 * The caller can keep the existing first-key order and recurse only within
 * each equal-key group.
 */
static bool
mkqs_sort_presorted_leading_groups(SortTuple *x,
								  size_t n,
								  Tuplesortstate *state)
{
	size_t		group_start = 0;

	Assert(state->base.nKeys > 1);

	for (size_t i = 1; i < n; i++)
	{
		int			ret;

		CHECK_FOR_INTERRUPTS();
		ret = comparetup_mk(x + i - 1, x + i, 0, 0, state);

		if (ret > 0)
			return false;

		if (ret < 0)
		{
			size_t		group_size = i - group_start;

			if (group_size > 1)
			{
				bool		isDatumNull;

				isDatumNull = check_datum_null(x + group_start, 0, state);
				mk_qsort_tuple(x + group_start,
							   group_size,
							   1,
							   state,
							   isDatumNull);
			}

			group_start = i;
		}
	}

	if (n - group_start > 1)
	{
		bool		isDatumNull;

		isDatumNull = check_datum_null(x + group_start, 0, state);
		mk_qsort_tuple(x + group_start,
					   n - group_start,
					   1,
					   state,
					   isDatumNull);
	}

	return true;
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
	MkqsPartitionCompareKind compareKind;
	MkqsPartitionBounds bounds;


	Assert(depth <= state->base.nKeys);
	Assert(state->base.sortKeys);
	Assert(state->base.mkqsTupleType != MKQS_TUPLE_TYPE_NONE);

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
	else if (mkqs_depth_strictly_increasing(x, n, depth, state))
		return;

	/*
	 * For radix-capable datums, preserve the existing first-key order and
	 * sort only ties by the remaining keys.
	 */
	if (depth == 0 &&
		state->base.nKeys > 1 &&
		state->base.mkqsCompFuncType != MKQS_COMP_FUNC_GENERIC &&
		!state->base.mkqsHandleDupFunc &&
		mkqs_sort_presorted_leading_groups(x, n, state))
		return;

	/*
	 * When the count < 16 and no need to handle duplicated tuples, use
	 * bubble sort.
	 *
	 * Use 16 instead of 7 which is used in standard qsort, because mk qsort
	 * need more cost to maintain more complex state.
	 *
	 * Bubble sort is not applicable for scenario of handle duplicated tuples
	 * because it is difficult to check NULL effectively.
	 *
	 * No need to check for interrupts since the data size is pretty small.
	 *
	 * TODO: Can we check NULL for bubble sort with minimal cost?
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

	compareKind = mkqs_select_partition_compare_kind(state, depth);
	if (compareKind == MKQS_PARTITION_COMPARE_GENERIC)
		mkqs_partition_generic(x, n, depth, state, &bounds);
	else if (compareKind == MKQS_PARTITION_COMPARE_HEAP_GENERIC)
		mkqs_partition_heap_generic(x, n, depth, state, &bounds);
	else
		mkqs_partition(x, n, depth, state, compareKind, &bounds);

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

#ifdef USE_ASSERT_CHECKING
	mkqs_verify(x,
				n,
				depth,
				state);
#endif
}

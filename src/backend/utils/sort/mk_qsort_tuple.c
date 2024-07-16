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

	state->base.mkqsGetDatumFunc(x, NULL, depth, state,
								 &datum, &isNull, NULL, NULL);

	return isNull;
}

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
mkqs_compare_datum_tiebreak(SortTuple *tuple1,
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

	Assert(state->base.mkqsGetDatumFunc);
	Assert(depth < state->base.nKeys);

	sortKey = state->base.sortKeys + depth;
	state->base.mkqsGetDatumFunc(tuple1,
								 tuple2,
								 depth,
								 state,
								 &datum1,
								 &isNull1,
								 &datum2,
								 &isNull2);

	/*
	 * If "abbreviated key" is enabled, and we are in the first depth, it
	 * means only "abbreviated keys" was compared. If the two datums were
	 * determined to be equal by ApplySortComparator() in
	 * mkqs_compare_datum(), we need to perform an extra "full" comparing
	 * by ApplySortAbbrevFullComparator().
	 */
	if (sortKey->abbrev_converter &&
		depth == 0)
		ret = ApplySortAbbrevFullComparator(datum1,
											isNull1,
											datum2,
											isNull2,
											sortKey);
	else
		ret = ApplySortComparator(datum1,
								  isNull1,
								  datum2,
								  isNull2,
								  sortKey);


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
	int ret = 0;
	MkqsCompFuncType compFuncType = state->base.mkqsCompFuncType;
	SortSupport sortKey = &state->base.sortKeys[0];

	if (compFuncType == MKQS_COMP_FUNC_UNSIGNED)
		ret = ApplyUnsignedSortComparator(tuple1->datum1,
										  tuple1->isnull1,
										  tuple2->datum1,
										  tuple2->isnull1,
										  sortKey);
#if SIZEOF_DATUM >= 8
	else if (compFuncType == MKQS_COMP_FUNC_SIGNED)
		ret = ApplySignedSortComparator(tuple1->datum1,
										tuple1->isnull1,
										tuple2->datum1,
										tuple2->isnull1,
										sortKey);
#endif
	else if (compFuncType == MKQS_COMP_FUNC_INT32)
		ret = ApplyInt32SortComparator(tuple1->datum1,
									   tuple1->isnull1,
									   tuple2->datum1,
									   tuple2->isnull1,
									   sortKey);
	else
	{
		Assert(compFuncType == MKQS_COMP_FUNC_GENERIC);
		ret = ApplySortComparator(tuple1->datum1,
								  tuple1->isnull1,
								  tuple2->datum1,
								  tuple2->isnull1,
								  sortKey);
	}

	return ret;
}

/*
 * Compare two tuples at specified depth
 *
 * Firstly try to call some shortcuts by mkqs_compare_datum_by_shortcut(),
 * which are much faster because they just compare leading sort keys; if they
 * are equal, call mkqs_compare_datum_tiebreak().
 *
 * The reason to use MkqsCompFuncType but not compare function pointers
 * directly is just for performance.
 *
 * See comparetup_heap() for details.
 */
static inline int
mkqs_compare_datum(SortTuple *tuple1,
				   SortTuple *tuple2,
				   int depth,
				   Tuplesortstate *state)
{
	int			ret = 0;

	if (depth == 0)
	{
		ret = mkqs_compare_datum_by_shortcut(tuple1, tuple2, state);

		if (ret != 0)
			return ret;

		/*
		 * If they are equal and it is not an abbr key, no need to
		 * continue.
		 */
		if (!state->base.sortKeys->abbrev_converter)
			return ret;
	}

	ret = mkqs_compare_datum_tiebreak(tuple1,
									  tuple2,
									  depth,
									  state);

	return ret;
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
	return mkqs_compare_datum(x + a, x + b, depth, state) < 0 ?
			 (mkqs_compare_datum(x + b, x + c, depth, state) < 0 ?
				b : (mkqs_compare_datum(x + a, x + c, depth, state) < 0 ? c : a))
			 : (mkqs_compare_datum(x + b, x + c, depth, state) > 0 ?
				b : (mkqs_compare_datum(x + a, x + c, depth, state) < 0 ? a : c));
}

/*
 * Compare two tuples by starting specified depth till latest depth
 */
static inline int
mkqs_compare_tuple_by_range_tiebreak(SortTuple *tuple1,
									 SortTuple *tuple2,
									 int depth,
									 Tuplesortstate *state)
{
	int			ret = 0;
	Datum		datum1,
				datum2;
	bool		isNull1,
				isNull2;
	const MkqsGetDatumFunc getDatumFunc = state->base.mkqsGetDatumFunc;
	SortSupport sortKey = state->base.sortKeys + depth;

	Assert(getDatumFunc);
	Assert(depth < state->base.nKeys);

	if (depth == 0)
	{
		/*
		 * If "abbreviated key" is enabled, and we are in the first depth, it
		 * means only "abbreviated keys" was compared. If the two datums were
		 * determined to be equal by ApplySortComparator() in
		 * mkqs_compare_datum(), we need to perform an extra "full" comparing
		 * by ApplySortAbbrevFullComparator().
		 */
		if (sortKey->abbrev_converter)
		{
			getDatumFunc(tuple1,
						 tuple2,
						 depth,
						 state,
						 &datum1,
						 &isNull1,
						 &datum2,
						 &isNull2);
			ret = ApplySortAbbrevFullComparator(datum1,
												isNull1,
												datum2,
												isNull2,
												sortKey);
			if (ret != 0)
				return ret;
		}

		/*
		 * By now, all works about first depth have been down. Move the
		 * depth and sortKey to next level.
		 */
		depth++;
		sortKey++;
	}

	while (depth < state->base.nKeys)
	{
		getDatumFunc(tuple1,
					 tuple2,
					 depth,
					 state,
					 &datum1,
					 &isNull1,
					 &datum2,
					 &isNull2);

		ret = ApplySortComparator(datum1,
								  isNull1,
								  datum2,
								  isNull2,
								  sortKey);

		if (ret != 0)
			return ret;

		depth++;
		sortKey++;
	}

	Assert(ret == 0);
	return 0;
}

/*
 * Compare two tuples by starting specified depth till latest depth
 *
 * Caller should guarantee that all datums before specified depth
 * are equal.
 *
 * If depth == 0, call mkqs_compare_datum_by_shortcut() to compare
 * compare leading sort keys. If they are equal, or depth != 0, call
 * mkqs_compare_tuple_by_range_tiebreak().
 */
static inline int
mkqs_compare_tuple_by_range(SortTuple *tuple1,
							SortTuple *tuple2,
							int depth,
							Tuplesortstate *state)
{
	if (depth == 0)
	{
		int ret = 0;

		ret = mkqs_compare_datum_by_shortcut(tuple1, tuple2, state);

		if (ret != 0)
			return ret;

		/*
		 * No need to check state->base.onlyKey to decide to call the
		 * tiebreak function like qsort_tuple_unsigned_compare(), 
		 * because mk qsort has at least two sort keys, i.e. we have
		 * to call tiebreak function anyway at the time.
		 */
	}

	return mkqs_compare_tuple_by_range_tiebreak(tuple1,
												tuple2,
												depth,
												state);
}

/*
 * Compare two tuples by using interfaces of qsort()
 */
static inline int
mkqs_compare_tuple(SortTuple *a, SortTuple *b, Tuplesortstate *state)
{
	int ret = 0;
	MkqsCompFuncType compFuncType = state->base.mkqsCompFuncType;

	/*
	 * The function should never be called with
	 * MKQS_COMP_FUNC_GENERIC
	 */
	Assert(compFuncType != MKQS_COMP_FUNC_GENERIC);

	if (compFuncType == MKQS_COMP_FUNC_UNSIGNED)
		ret = qsort_tuple_unsigned_compare(a, b, state);
#if SIZEOF_DATUM >= 8
	else if (compFuncType == MKQS_COMP_FUNC_SIGNED)
		ret = qsort_tuple_signed_compare(a, b, state);
#endif
	else if (compFuncType == MKQS_COMP_FUNC_INT32)
		ret = qsort_tuple_int32_compare(a, b, state);
	else
		Assert(false);

	return ret;
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
		ret = mkqs_compare_datum(x + i,
								 x + i + 1,
								 depth,
								 state);
		Assert(ret <= 0);
	}
}
#endif

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
				tupCount;
	int32		dist;
	SortTuple  *pivot;
	bool		isDatumNull;

	Assert(depth <= state->base.nKeys);
	Assert(state->base.sortKeys);
	Assert(state->base.mkqsGetDatumFunc);

	if (n <= 1)
		return;

	/* If we have exceeded the max depth, return immediately */
	if (depth == state->base.nKeys)
		return;

	CHECK_FOR_INTERRUPTS();

	/* Pre-ordered check */
	if (state->base.mkqsCompFuncType != MKQS_COMP_FUNC_GENERIC)
	{
		/*
		 * If there is specialized comparator for the type, use classic
		 * pre-ordered check by comparing the entire tuples.
		 * The check is performed only for first depth since we compare
		 * entire tuples but not datums.
		 */
		if (depth == 0)
		{
			int ret;
			bool preOrdered = true;

			for (int i = 0; i < n - 1; i++)
			{

				CHECK_FOR_INTERRUPTS();
				ret = mkqs_compare_tuple(x + i, x + i + 1, state);
				if (ret > 0)
				{
					preOrdered = false;
					break;
				}
			}

			if (preOrdered)
				return;
		}
	}
	else
	{
		/*
		 * If there is no specialized comparator for the type, perform
		 * pre-ordered check by comparing datums at each depth.
		 *
		 * Different from qsort_tuple(), the array must be strict ordered (no
		 * equal datums). If there are equal datums, we must continue the mk
		 * qsort process to check datums on lower depth.
		 *
		 * Note uniqueness check is unnecessary here because strict ordered
		 * array guarantees no duplicate.
		 */
		int ret;
		bool strictOrdered = true;

		for (int i = 0; i < n - 1; i++)
		{
			CHECK_FOR_INTERRUPTS();
			ret = mkqs_compare_datum(x + i,
									 x + i + 1,
									 depth,
									 state);
			if (ret >= 0)
			{
				strictOrdered = false;
				break;
			}
		}

		if (strictOrdered)
			return;
	}

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
	if (n < 16 && !state->base.mkqsHandleDupFunc)
	{
		for (int m = 0;m < n;m++)
			for (int l = m; l > 0; l--)
			{
				if (mkqs_compare_tuple_by_range(x + l - 1, x + l, depth, state)
					<= 0)
					break;
				mkqs_swap(l, l - 1, x);
			}
		return;
	}

	/* Select pivot by random and move it to the first position */
	if (n > 7)
	{
		int m, l, r, d;
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
	}
	else
		lessStart = n / 2;

	mkqs_swap(0, lessStart, x);
	pivot = x;

	lessStart = 1;
	lessEnd = 1;
	greaterStart = n - 1;
	greaterEnd = n - 1;

	/* Sort the array to three parts: lesser, equal, greater */
	while (true)
	{
		CHECK_FOR_INTERRUPTS();

		/* Compare the left end of the array */
		while (lessEnd <= greaterStart)
		{
			/* Compare lessEnd and pivot at current depth */
			dist = mkqs_compare_datum(x + lessEnd,
									  pivot,
									  depth,
									  state);

			if (dist > 0)
				break;

			/* If lessEnd is equal to pivot, move it to lessStart */
			if (dist == 0)
			{
				mkqs_swap(lessEnd, lessStart, x);
				lessStart++;
			}
			lessEnd++;
		}

		/* Compare the right end of the array */
		while (lessEnd <= greaterStart)
		{
			/* Compare greaterStart and pivot at current depth */
			dist = mkqs_compare_datum(x + greaterStart,
									  pivot,
									  depth,
									  state);

			if (dist < 0)
				break;

			/* If greaterStart is equal to pivot, move it to greaterEnd */
			if (dist == 0)
			{
				mkqs_swap(greaterStart, greaterEnd, x);
				greaterEnd--;
			}
			greaterStart--;
		}

		if (lessEnd > greaterStart)
			break;
		mkqs_swap(lessEnd, greaterStart, x);
		lessEnd++;
		greaterStart--;
	}

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
		 * Call mkqsHandleDupFunc if:
		 *  1. mkqsHandleDupFunc is filled
		 *  2. the size of equal part > 1
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

/*-------------------------------------------------------------------------
 *
 * mk_qsort_tuple_template.h
 *	  Template for a heap tuple comparator used by multi-key quicksort.
 *
 * Copyright (c) 2026, PostgreSQL Global Development Group
 *
 * Usage notes:
 *
 *	  The following parameter macros should be defined before this file is
 *	  included:
 *
 *	  - MKQS_COMPARE - name of the comparator function to generate
 *	  - MKQS_COMPARE_TYPE - C type used for comparison
 *	  - MKQS_COMPARE_DATUM_GETTER - convert Datum to MKQS_COMPARE_TYPE
 *
 * IDENTIFICATION
 *	  src/backend/utils/sort/mk_qsort_tuple_template.h
 *
 *-------------------------------------------------------------------------
 */

#if !defined(MKQS_COMPARE) || !defined(MKQS_COMPARE_TYPE) || \
	!defined(MKQS_COMPARE_DATUM_GETTER)
#error "MKQS comparator template parameters must be defined"
#endif

static pg_attribute_always_inline int
MKQS_COMPARE(SortTuple *tuple1, SortTuple *tuple2,
			 SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum1;
	Datum		datum2;
	bool		isNull1;
	bool		isNull2;
	int			compare;

	mkqs_get_heap_datums(tuple1, tuple2, sortKey, state,
						 &datum1, &isNull1, &datum2, &isNull2);
	compare = mkqs_compare_nulls(isNull1, isNull2, sortKey);
	if (compare == MKQS_COMPARE_NONNULL)
	{
		MKQS_COMPARE_TYPE value1 = MKQS_COMPARE_DATUM_GETTER(datum1);
		MKQS_COMPARE_TYPE value2 = MKQS_COMPARE_DATUM_GETTER(datum2);

		compare = (value1 > value2) - (value1 < value2);
		if (sortKey->ssup_reverse)
			INVERT_COMPARE_RESULT(compare);
	}

	return compare;
}

#undef MKQS_COMPARE
#undef MKQS_COMPARE_DATUM_GETTER
#undef MKQS_COMPARE_TYPE

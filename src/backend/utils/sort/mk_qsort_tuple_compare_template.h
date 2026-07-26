/*-------------------------------------------------------------------------
 *
 * mk_qsort_tuple_compare_template.h
 *	  Template for a typed comparator and partition used by multi-key quicksort.
 *
 * Copyright (c) 2026, PostgreSQL Global Development Group
 *
 * Usage notes:
 *
 *	  The following parameter macros should be defined before this file is
 *	  included:
 *
 *	  - MKQS_COMPARE - name of the comparator function to generate
 *	  - MKQS_PARTITION - name of the partition function to generate
 *	  - MKQS_COMPARE_TYPE - C type used for comparison
 *	  - MKQS_COMPARE_DATUM_GETTER - convert Datum to MKQS_COMPARE_TYPE
 *	  - MKQS_COMPARE_GET_DATUM - extract a datum from the input tuple
 *
 * IDENTIFICATION
 *	  src/backend/utils/sort/mk_qsort_tuple_compare_template.h
 *
 *-------------------------------------------------------------------------
 */

#if !defined(MKQS_COMPARE) || !defined(MKQS_PARTITION) || \
	!defined(MKQS_COMPARE_TYPE) || \
	!defined(MKQS_COMPARE_DATUM_GETTER) || \
	!defined(MKQS_COMPARE_GET_DATUM)
#error "MKQS comparator template parameters must be defined"
#endif

static pg_attribute_always_inline int
MKQS_COMPARE(SortTuple *tuple, Datum pivotDatum, bool pivotIsNull,
			 SortSupport sortKey, Tuplesortstate *state)
{
	Datum		datum;
	bool		isNull;
	int			compare;

	datum = MKQS_COMPARE_GET_DATUM(tuple, sortKey, state, &isNull);
	if (isNull || pivotIsNull)
	{
		if (isNull && pivotIsNull)
			return 0;

		return isNull == sortKey->ssup_nulls_first ? -1 : 1;
	}

	{
		MKQS_COMPARE_TYPE value = MKQS_COMPARE_DATUM_GETTER(datum);
		MKQS_COMPARE_TYPE pivotValue =
			MKQS_COMPARE_DATUM_GETTER(pivotDatum);

		compare = (value > pivotValue) - (value < pivotValue);
	}
	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(compare);

	return compare;
}

/* Cache the pivot datum once and keep the typed comparison in the hot loop. */
#define MKQS_PARTITION_SCOPE static pg_noinline
#define MKQS_PARTITION_EXTRA_DECLARATIONS \
	SortSupport sortKey; \
	Datum		pivotDatum; \
	bool		pivotIsNull;
#define MKQS_PARTITION_SETUP() \
	do { \
		sortKey = &state->base.sortKeys[depth]; \
		pivotDatum = MKQS_COMPARE_GET_DATUM(pivot, sortKey, state, \
										 &pivotIsNull); \
	} while (0)
#define MKQS_PARTITION_COMPARE(tuple) \
	MKQS_COMPARE((tuple), pivotDatum, pivotIsNull, sortKey, state)
#include "mk_qsort_tuple_partition_template.h"

#undef MKQS_COMPARE
#undef MKQS_COMPARE_DATUM_GETTER
#undef MKQS_COMPARE_GET_DATUM
#undef MKQS_COMPARE_TYPE

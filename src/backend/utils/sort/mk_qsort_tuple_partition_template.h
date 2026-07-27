/*-------------------------------------------------------------------------
 *
 * mk_qsort_tuple_partition_template.h
 *	  Template for a three-way multi-key quicksort partition.
 *
 * Copyright (c) 2026, PostgreSQL Global Development Group
 *
 * Usage notes:
 *
 *	  The following parameter macros should be defined before this file is
 *	  included:
 *
 *	  - MKQS_PARTITION - name of the partition function to generate
 *
 *	  A generic partition must also define:
 *
 *	  - MKQS_PARTITION_COMPARE(tuple) - compare tuple with the pivot
 *
 *	  A typed partition must instead define all of:
 *
 *	  - MKQS_PARTITION_TYPE - C type used for comparison
 *	  - MKQS_PARTITION_DATUM_GETTER - convert Datum to MKQS_PARTITION_TYPE
 *	  - MKQS_PARTITION_GET_DATUM - extract a datum from the input tuple
 *
 *	  The following parameter macros are optional:
 *
 *	  - MKQS_PARTITION_SCOPE - scope and attributes for the generated function
 *	  - MKQS_PARTITION_EXTRA_DECLARATIONS - extra function-local declarations
 *	  - MKQS_PARTITION_SETUP() - initialize comparator-specific local state
 *
 * IDENTIFICATION
 *	  src/backend/utils/sort/mk_qsort_tuple_partition_template.h
 *
 *-------------------------------------------------------------------------
 */

#if !defined(MKQS_PARTITION)
#error "MKQS_PARTITION must be defined"
#endif

#if defined(MKQS_PARTITION_TYPE) || \
	defined(MKQS_PARTITION_DATUM_GETTER) || \
	defined(MKQS_PARTITION_GET_DATUM)
#if !defined(MKQS_PARTITION_TYPE) || \
	!defined(MKQS_PARTITION_DATUM_GETTER) || \
	!defined(MKQS_PARTITION_GET_DATUM)
#error "all typed MKQS partition parameters must be defined"
#endif
#ifdef MKQS_PARTITION_COMPARE
#error "typed MKQS partitions generate their own comparator"
#endif

#define MKQS_TYPED_COMPARE_NAME_(name) name##_compare
#define MKQS_TYPED_COMPARE_NAME(name) MKQS_TYPED_COMPARE_NAME_(name)

/* This helper is private to its typed partition and is always inlined. */
static pg_attribute_always_inline int
MKQS_TYPED_COMPARE_NAME(MKQS_PARTITION)(SortTuple *tuple,
										Datum pivotDatum,
										bool pivotIsNull,
										SortSupport sortKey,
										Tuplesortstate *state)
{
	Datum		datum;
	bool		isNull;
	int			compare;

	datum = MKQS_PARTITION_GET_DATUM(tuple, sortKey, state, &isNull);
	if (isNull || pivotIsNull)
	{
		if (isNull && pivotIsNull)
			return 0;

		return isNull == sortKey->ssup_nulls_first ? -1 : 1;
	}

	{
		MKQS_PARTITION_TYPE value = MKQS_PARTITION_DATUM_GETTER(datum);
		MKQS_PARTITION_TYPE pivotValue =
			MKQS_PARTITION_DATUM_GETTER(pivotDatum);

		compare = (value > pivotValue) - (value < pivotValue);
	}
	if (sortKey->ssup_reverse)
		INVERT_COMPARE_RESULT(compare);

	return compare;
}

/* Cache the pivot datum once and keep the typed comparison in the hot loop. */
#define MKQS_PARTITION_EXTRA_DECLARATIONS \
	SortSupport sortKey; \
	Datum		pivotDatum; \
	bool		pivotIsNull;
#define MKQS_PARTITION_SETUP() \
	do { \
		sortKey = &state->base.sortKeys[depth]; \
		pivotDatum = MKQS_PARTITION_GET_DATUM(pivot, sortKey, state, \
											&pivotIsNull); \
	} while (0)
#define MKQS_PARTITION_COMPARE(tuple) \
	MKQS_TYPED_COMPARE_NAME(MKQS_PARTITION)((tuple), pivotDatum, \
										pivotIsNull, sortKey, state)
#elif !defined(MKQS_PARTITION_COMPARE)
#error "generic MKQS partitions must define MKQS_PARTITION_COMPARE"
#endif

#ifndef MKQS_PARTITION_SCOPE
#define MKQS_PARTITION_SCOPE static pg_noinline
#endif

#ifndef MKQS_PARTITION_EXTRA_DECLARATIONS
#define MKQS_PARTITION_EXTRA_DECLARATIONS
#endif

#ifndef MKQS_PARTITION_SETUP
#define MKQS_PARTITION_SETUP() ((void) 0)
#endif

MKQS_PARTITION_SCOPE void
MKQS_PARTITION(SortTuple *x, size_t n, int depth,
			   Tuplesortstate *state, MkqsPartitionBounds *bounds)
{
	SortTuple  *pivot = x;
	int32		dist;
	MKQS_PARTITION_EXTRA_DECLARATIONS

	bounds->lessStart = 1;
	bounds->lessEnd = 1;
	bounds->greaterStart = n - 1;
	bounds->greaterEnd = n - 1;
	MKQS_PARTITION_SETUP();

	while (true)
	{
		CHECK_FOR_INTERRUPTS();

		while (bounds->lessEnd <= bounds->greaterStart)
		{
			dist = MKQS_PARTITION_COMPARE(x + bounds->lessEnd);
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
			dist = MKQS_PARTITION_COMPARE(x + bounds->greaterStart);
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

#undef MKQS_PARTITION
#undef MKQS_PARTITION_COMPARE
#undef MKQS_PARTITION_EXTRA_DECLARATIONS
#undef MKQS_PARTITION_SCOPE
#undef MKQS_PARTITION_SETUP
#undef MKQS_TYPED_COMPARE_NAME
#undef MKQS_TYPED_COMPARE_NAME_
#undef MKQS_PARTITION_DATUM_GETTER
#undef MKQS_PARTITION_GET_DATUM
#undef MKQS_PARTITION_TYPE

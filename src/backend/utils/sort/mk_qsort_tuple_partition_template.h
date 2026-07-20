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
 *	  - MKQS_PARTITION_SCOPE - scope and attributes for the generated function
 *	  - MKQS_PARTITION_COMPARE(tuple) - compare tuple with the pivot
 *
 *	  The following parameter macros are optional:
 *
 *	  - MKQS_PARTITION_EXTRA_DECLARATIONS - extra function-local declarations
 *	  - MKQS_PARTITION_SETUP() - initialize comparator-specific local state
 *
 * IDENTIFICATION
 *	  src/backend/utils/sort/mk_qsort_tuple_partition_template.h
 *
 *-------------------------------------------------------------------------
 */

#if !defined(MKQS_PARTITION) || !defined(MKQS_PARTITION_SCOPE) || \
	!defined(MKQS_PARTITION_COMPARE)
#error "MKQS partition template parameters must be defined"
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

/*-------------------------------------------------------------------------
 *
 * mk_qsort_tuple_partition_template.h
 *	  Template for a tuple-representation-specific mksort partition.
 *
 * Copyright (c) 2026, PostgreSQL Global Development Group
 *
 * Before including this file, define:
 *
 * MKQS_PARTITION
 *	  Name of the partition function to generate.
 *
 * MKQS_COMPARE_TO_PIVOT
 *	  Name of the always-inline pivot comparison function to generate.
 *
 * MKQS_GET_DATUM
 *	  Inline function that extracts the current sort key's datum from a
 *	  SortTuple.
 *
 * MKQS_COMPARE_DATUM
 *	  Inline function that applies NULL and sort-direction semantics around
 *	  the supplied typed datum comparator.
 *
 * IDENTIFICATION
 *	  src/backend/utils/sort/mk_qsort_tuple_partition_template.h
 *
 *-------------------------------------------------------------------------
 */

#if !defined(MKQS_PARTITION) || !defined(MKQS_COMPARE_TO_PIVOT) || \
	!defined(MKQS_GET_DATUM) || \
	!defined(MKQS_COMPARE_DATUM)
#error "MKQS partition template parameters must be defined"
#endif

/* Compare one tuple with the cached pivot using the specialized accessor. */
static pg_attribute_always_inline int
MKQS_COMPARE_TO_PIVOT(SortTuple *tuple, int depth,
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
		compare = MKQS_COMPARE_DATUM(tuple->datum1, tuple->isnull1,
									 pivotDatum, pivotIsNull, sortKey,
									 compare_datum_typed);
		if (compare != 0 || !sortKey->abbrev_converter ||
			tuple->isnull1 || pivotIsNull)
			return compare;

		datum = MKQS_GET_DATUM(tuple, sortKey, state, &isNull);
		Assert(!isNull);
		return MKQS_COMPARE_DATUM(datum, false, pivotFullDatum, false,
								  sortKey, sortKey->abbrev_full_comparator);
	}

	datum = MKQS_GET_DATUM(tuple, sortKey, state, &isNull);
	return MKQS_COMPARE_DATUM(datum, isNull, pivotDatum, pivotIsNull,
							  sortKey, compare_datum_typed);
}

/* Partition tuples around x[0], comparing only the current key depth. */
static bool
MKQS_PARTITION(SortTuple *x, size_t n, int depth,
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

			pivotFullDatum = MKQS_GET_DATUM(x, sortKey, state, &isNull);
			Assert(!isNull);
		}
	}
	else
		pivotDatum = MKQS_GET_DATUM(x, sortKey, state, &pivotIsNull);

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
			dist = MKQS_COMPARE_TO_PIVOT(x + bounds->lessEnd, depth,
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
			dist = MKQS_COMPARE_TO_PIVOT(x + bounds->greaterStart, depth,
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

#undef MKQS_COMPARE_TO_PIVOT
#undef MKQS_COMPARE_DATUM
#undef MKQS_GET_DATUM
#undef MKQS_PARTITION

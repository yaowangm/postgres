/*-------------------------------------------------------------------------
 *
 * tuplesortvariants.h
 *	  Private declarations shared by tuplesort implementation files.
 *
 * IDENTIFICATION
 *	  src/backend/utils/sort/tuplesortvariants.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef TUPLESORTVARIANTS_H
#define TUPLESORTVARIANTS_H

#include "utils/rel.h"

/* Common prefix of the private state for each index tuple sort variant. */
typedef struct TuplesortIndexArg
{
	TupleDesc	tupDesc;		/* cached descriptor for index tuples */
	Relation	heapRel;		/* table the index is being built on */
	Relation	indexRel;		/* index being built */
} TuplesortIndexArg;

#endif							/* TUPLESORTVARIANTS_H */

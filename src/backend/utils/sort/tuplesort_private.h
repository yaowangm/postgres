/*-------------------------------------------------------------------------
 *
 * tuplesort_private.h
 *	  Private declarations shared by tuplesort implementation files.
 *
 * Copyright (c) 2026, PostgreSQL Global Development Group
 *
 * IDENTIFICATION
 *	  src/backend/utils/sort/tuplesort_private.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef TUPLESORT_PRIVATE_H
#define TUPLESORT_PRIVATE_H

#include "utils/rel.h"

/* Common prefix of the private state for each index tuple sort variant. */
typedef struct TuplesortIndexArg
{
	Relation	heapRel;		/* table the index is being built on */
	Relation	indexRel;		/* index being built */
} TuplesortIndexArg;

#endif							/* TUPLESORT_PRIVATE_H */

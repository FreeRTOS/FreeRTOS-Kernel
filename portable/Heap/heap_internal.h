//=================
// heap_internal.h
//=================

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap

#ifndef _HEAP_INTERNAL_H
#define _HEAP_INTERNAL_H


//=======
// Using
//=======

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define MPU_WRAPPERS_INCLUDED_FROM_API_FILE

#include "FreeRTOS.h"
#include "task.h"

#undef MPU_WRAPPERS_INCLUDED_FROM_API_FILE


//==========
// Settings
//==========

#define configUSE_HEAP_IN_ISR 1

#define CLUSTER_GROUP_SIZE 10


//===========
// Alignment
//===========

#define SIZE_BITS (sizeof(size_t)*8)
#define SIZE_BYTES sizeof(size_t)

#define BLOCK_SIZE_MIN (4*SIZE_BYTES)

static inline size_t align_down(size_t value, size_t align)
{
return value&~(align-1);
}

static inline size_t align_up(size_t value, size_t align)
{
return value+(align-value%align)%align;
}

#endif // _HEAP_INTERNAL_H

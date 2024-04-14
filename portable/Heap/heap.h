//========
// heap.h
//========

// Memory-manager for real-time C++ applications.
// Allocations and deletions are done in constant low time.

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


#ifndef _HEAP_H
#define _HEAP_H


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


//======
// Heap
//======

typedef struct _heap_t
{
size_t free;
size_t used;
size_t size;
size_t free_block;
size_t next_heap;
size_t map_free;
}heap_t;

typedef heap_t* heap_handle_t;


//==========
// Creation
//==========

heap_handle_t heap_create(heap_handle_t prev_heap, size_t offset, size_t size);


//============
// Allocation
//============

void* heap_alloc(heap_handle_t heap, size_t size);
void heap_free(heap_handle_t heap, void* buffer);


//=====================
// Internal Allocation
//=====================

void* heap_alloc_from_foot(heap_handle_t heap, size_t size);
void* heap_alloc_from_map(heap_handle_t heap, size_t size);
void* heap_alloc_internal(heap_handle_t heap, size_t size);
void heap_free_cache(heap_handle_t heap);
void heap_free_to_cache(heap_handle_t heap, void* buf);
void heap_free_to_map(heap_handle_t heap, void* buf);


//===========
// Statistic
//===========

size_t heap_get_largest_free_block(heap_handle_t heap);


//==========
// FreeRTOS
//==========

void* pvPortCalloc(size_t xNum, size_t xSize);
void* pvPortMalloc(size_t xWantedSize);
void vPortDefineHeapRegions(HeapRegion_t const* pxHeapRegions)PRIVILEGED_FUNCTION;
void vPortFree(void* pv);
void vPortGetHeapStats(HeapStats_t* pxHeapStats);
void vPortHeapResetState(void);
size_t xPortGetFreeHeapSize(void);
size_t xPortGetMinimumEverFreeHeapSize(void);

#endif // _HEAP_H

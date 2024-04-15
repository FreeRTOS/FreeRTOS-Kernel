//========
// heap.c
//========

// Memory-manager for real-time C++ applications.
// Allocations and deletions are done in constant low time.

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


//=======
// Using
//=======

#include "block_map.h"
#include "semphr.h"


//========
// Macros
//========

// These macros are from heap_5.c

#if(configSUPPORT_DYNAMIC_ALLOCATION==0)
#error This file must not be used if configSUPPORT_DYNAMIC_ALLOCATION is 0
#endif

#if(configHEAP_CLEAR_MEMORY_ON_FREE==1)
#error Not supported with heap_6
#endif

#if(configENABLE_HEAP_PROTECTOR==1)
#error Not supported with heap_6
#endif

/* Check if multiplying a and b will result in overflow. */
#define MULTIPLY_WILL_OVERFLOW(a, b) (((a)>0)&&((b)>(SIZE_MAX/(a))))

/* Check if adding a and b will result in overflow. */
#define ADD_WILL_OVERFLOW(a, b) ((a)>(SIZE_MAX-(b)))

/* Check if the subtraction operation (a-b) will result in underflow. */
#define SUBTRACT_WILL_UNDERFLOW(a, b) ((a)<(b))


static inline bool heap_lock()
{
#if(configUSE_HEAP_IN_ISR==1)
vTaskSuspendAll();
return true;
#else
taskENTER_CRITICAL();
if(xSemaphoreTake(heap_mutex, portMAX_DELAY)==pdTRUE)
	return true;
return false;
#endif
}

static inline void heap_unlock(bool locked)
{
#if(configUSE_HEAP_IN_ISR==1)
xTaskResumeAll();
#else
if(locked)
	xSemaphoreGive(heap_lock);
taskEXIT_CRITICAL();
#endif
}


//=========
// Globals
//=========

#if(configUSE_HEAP_IN_ISR==0)
static SemaphoreHandle_t heap_mutex=NULL;
static StaticSemaphore_t heap_mutex_buf;
#endif

static heap_handle_t first_heap=NULL;
static heap_handle_t last_heap=NULL;

static size_t xFreeBlocks=0;
static size_t xFreeBytes=0;
static size_t xMinimumFreeBytes=0;
static size_t xSuccessfulAllocations=0;
static size_t xSuccessfulDeletions=0;

static inline void heap_reduce_free_bytes(size_t reduce)
{
xFreeBytes-=reduce;
xMinimumFreeBytes=min(xMinimumFreeBytes, xFreeBytes);
}


//==========
// Creation
//==========

heap_handle_t heap_create(heap_handle_t prev_heap, size_t offset, size_t size)
{
offset=align_up(offset, sizeof(size_t));
size=align_down(size, sizeof(size_t));
configASSERT(size>sizeof(heap_t));
size_t available=size-sizeof(heap_t);
heap_handle_t heap=(heap_t*)offset;
heap->free=available;
heap->used=sizeof(heap_t);
heap->size=size;
heap->free_block=0;
heap->next_heap=0;
block_map_init((block_map_t*)&heap->map_free);
if(prev_heap)
	prev_heap->next_heap=(size_t)heap;
xFreeBlocks++;
xFreeBytes+=available;
xMinimumFreeBytes=xFreeBytes;
return heap;
}


//============
// Allocation
//============

void* heap_alloc(heap_handle_t heap, size_t size)
{
configASSERT(heap!=NULL);
configASSERT(size!=0);
size=heap_block_calc_size(size);
void* buf=heap_alloc_from_map(heap, size);
if(buf)
	{
	heap_free_cache(heap);
	}
else
	{
	buf=heap_alloc_from_foot(heap, size);
	}
return buf;
}

void heap_free(heap_handle_t heap, void* buf)
{
configASSERT(heap!=NULL);
if(!buf)
	return;
heap_free_to_map(heap, buf);
heap_free_cache(heap);
}


//=====================
// Internal Allocation
//=====================

void* heap_alloc_from_foot(heap_handle_t heap, size_t size)
{
if(heap->used+size>heap->size)
	return NULL;
heap_block_info_t info;
info.offset=(size_t)heap+heap->used;
info.size=size;
info.free=false;
heap->free-=size;
heap->used+=size;
heap_reduce_free_bytes(size);
return heap_block_init(heap, &info);
}

void* heap_alloc_from_map(heap_handle_t heap, size_t size)
{
heap_block_info_t info;
if(!block_map_get_block(heap, (block_map_t*)&heap->map_free, size, &info))
	return NULL;
heap->free-=info.size;
heap_reduce_free_bytes(info.size);
size_t free_size=info.size-size;
if(free_size>=BLOCK_SIZE_MIN)
	{
	heap_block_info_t free_info;
	free_info.offset=info.offset+size;
	free_info.size=free_size;
	free_info.free=false;
	void* free_buf=heap_block_init(heap, &free_info);
	heap_free_to_cache(heap, free_buf);
	info.size=size;
	}
xFreeBlocks--;
info.free=false;
return heap_block_init(heap, &info);
}

void* heap_alloc_internal(heap_handle_t heap, size_t size)
{
size=heap_block_calc_size(size);
void* buf=heap_alloc_from_map(heap, size);
if(buf)
	return buf;
return heap_alloc_from_foot(heap, size);
}

void heap_free_cache(heap_handle_t heap)
{
heap_t* heap_ptr=(heap_t*)heap;
size_t free_block=heap_ptr->free_block;
if(!free_block)
	return;
size_t* buf=(size_t*)heap_block_get_pointer(free_block);
heap_ptr->free_block=*buf;
heap_free_to_map(heap, buf);
}

void heap_free_to_cache(heap_handle_t heap, void* buf)
{
size_t* body_ptr=(size_t*)buf;
*body_ptr=heap->free_block;
heap->free_block=heap_block_get_offset(buf);
}

void heap_free_to_map(heap_handle_t heap, void* buf)
{
heap_block_chain_t info;
heap_block_get_chain(heap, buf, &info);
size_t heap_end=(size_t)heap+heap->used;
size_t offset=info.current.offset;
size_t size=info.current.size;
configASSERT(offset>=(size_t)heap);
configASSERT(offset<heap_end);
configASSERT(offset+size<=heap_end);
if(info.previous.free)
	{
	offset=info.previous.offset;
	size+=info.previous.size;
	block_map_remove_block(heap, (block_map_t*)&heap->map_free, &info.previous);
	heap->free-=info.previous.size;
	xFreeBlocks--;
	xFreeBytes-=info.previous.size;
	}
if(!info.next.offset)
	{
	heap->free+=size;
	heap->used-=size;
	xFreeBytes+=size;
	return;
	}
if(info.next.free)
	{
	size+=info.next.size;
	block_map_remove_block(heap, (block_map_t*)&heap->map_free, &info.next);
	heap->free-=info.next.size;
	xFreeBlocks--;
	xFreeBytes-=info.next.size;
	}
info.current.offset=offset;
info.current.size=size;
info.current.free=true;
heap_block_init(heap, &info.current);
bool added=block_map_add_block(heap, (block_map_t*)&heap->map_free, &info.current);
if(!added)
	{
	info.current.free=false;
	heap_block_init(heap, &info.current);
	buf=heap_block_get_pointer(info.current.offset);
	heap_free_to_cache(heap, buf);
	return;
	}
heap->free+=size;
xFreeBlocks++;
xFreeBytes+=size;
}


//===========
// Statistic
//===========

size_t heap_get_largest_free_block(heap_handle_t heap)
{
size_t largest=0;
largest=block_map_get_last_size((block_map_t*)&heap->map_free);
largest=max(largest, heap->size-heap->used);
return largest;
}


//==========
// FreeRTOS
//==========

void* pvPortCalloc(size_t xNum, size_t xSize)
{
void* buf=NULL;
if(MULTIPLY_WILL_OVERFLOW(xNum, xSize)==0)
	{
	buf=pvPortMalloc(xNum*xSize);
	if(buf!=NULL)
		memset(buf, 0, xNum*xSize);
	}
return buf;
}

void* pvPortMalloc(size_t xWantedSize)
{
void* buf=NULL;
bool locked=heap_lock();
if(locked)
	{
	heap_handle_t heap=first_heap;
	while(heap)
		{
		buf=heap_alloc(heap, xWantedSize);
		if(buf!=NULL)
			break;
		heap=(heap_handle_t)heap->next_heap;
		}
	}
heap_unlock(locked);
if(buf!=NULL)
	xSuccessfulAllocations++;
return buf;
}

void vPortDefineHeapRegions(HeapRegion_t const* pxHeapRegions)PRIVILEGED_FUNCTION
{
configASSERT(first_heap==NULL);
configASSERT(pxHeapRegions!=NULL);
HeapRegion_t const* region=pxHeapRegions;
while(region->xSizeInBytes>0)
	{
	size_t offset=(size_t)region->pucStartAddress;
	size_t size=region->xSizeInBytes;
	heap_handle_t heap=heap_create(last_heap, offset, size);
	configASSERT(heap!=NULL);
	if(first_heap==NULL)
		first_heap=heap;
	last_heap=heap;
	region++;
	}
#if(configUSE_HEAP_IN_ISR==0)
heap_mutex=xSemaphoreCreateMutexStatic(&heap_mutex_buf);
#endif
}

void vPortFree(void* pv)
{
if(pv==NULL)
	return;
size_t offset=(size_t)pv;
bool locked=heap_lock();
if(locked)
	{
	heap_handle_t heap=first_heap;
	while(heap)
		{
		size_t heap_start=(size_t)heap;
		size_t heap_end=heap_start+heap->size;
		if(offset>heap_start&&offset<heap_end)
			{
			heap_free(heap, pv);
			xSuccessfulDeletions++;
			break;
			}
		heap=(heap_handle_t)heap->next_heap;
		}
	}
heap_unlock(locked);
}

void vPortGetHeapStats(HeapStats_t* pxHeapStats)
{
configASSERT(pxHeapStats!=NULL);
memset(pxHeapStats, 0, sizeof(HeapStats_t));
bool locked=heap_lock();
if(locked)
	{
	size_t largest=0;
	heap_handle_t heap=first_heap;
	while(heap)
		{
		largest=max(largest, heap_get_largest_free_block(heap));
		heap=(heap_handle_t)heap->next_heap;
		}
	pxHeapStats->xAvailableHeapSpaceInBytes=xFreeBytes;
	pxHeapStats->xMinimumEverFreeBytesRemaining=xMinimumFreeBytes;
	pxHeapStats->xNumberOfFreeBlocks=xFreeBlocks;
	pxHeapStats->xNumberOfSuccessfulAllocations=xSuccessfulAllocations;
	pxHeapStats->xNumberOfSuccessfulFrees=xSuccessfulDeletions;
	pxHeapStats->xSizeOfLargestFreeBlockInBytes=largest;
	pxHeapStats->xSizeOfSmallestFreeBlockInBytes=BLOCK_SIZE_MIN;
	}
heap_unlock(locked);
}

void vPortHeapResetState(void)
{
#if(configUSE_HEAP_IN_ISR==0)
vSemaphoreDelete(heap_mutex);
heap_mutex=NULL;
#endif
first_heap=NULL;
last_heap=NULL;
xFreeBlocks=0;
xFreeBytes=0;
xMinimumFreeBytes=0;
xSuccessfulAllocations=0;
xSuccessfulDeletions=0;
}

size_t xPortGetFreeHeapSize(void)
{
return xFreeBytes;
}

size_t xPortGetMinimumEverFreeHeapSize(void)
{
return xMinimumFreeBytes;
}

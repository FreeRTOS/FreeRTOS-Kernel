//==========
// heap_6.h
//==========

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

#if(configSUPPORT_DYNAMIC_ALLOCATION==0)
#error This file must not be used if configSUPPORT_DYNAMIC_ALLOCATION is 0
#endif

#if(configHEAP_CLEAR_MEMORY_ON_FREE==1)
#error Not supported with heap_6
#endif

#if(configENABLE_HEAP_PROTECTOR==1)
#error Not supported with heap_6
#endif


//========
// Macros
//========

// These macros are from heap_5.c

/* Check if multiplying a and b will result in overflow. */
#define MULTIPLY_WILL_OVERFLOW(a, b) (((a)>0)&&((b)>(SIZE_MAX/(a))))


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


// Creation
heap_handle_t heap_create(heap_handle_t prev_heap, size_t offset, size_t size);


// Allocation
void* heap_alloc(heap_handle_t heap, size_t size);
void heap_free(heap_handle_t heap, void* buffer);


// Internal Allocation
void* heap_alloc_from_foot(heap_handle_t heap, size_t size);
void* heap_alloc_from_map(heap_handle_t heap, size_t size);
void* heap_alloc_internal(heap_handle_t heap, size_t size);
void heap_free_cache(heap_handle_t heap);
void heap_free_to_cache(heap_handle_t heap, void* buf);
void heap_free_to_map(heap_handle_t heap, void* buf);


// Statistic
size_t heap_get_largest_free_block(heap_handle_t heap);


//============
// Heap-Block
//============

typedef struct heap_block_info_t
{
size_t offset;
union
	{
	struct
		{
		size_t size: SIZE_BITS-1;
		size_t free: 1;
		};
	size_t header;
	};
}heap_block_info_t;

typedef struct
{
heap_block_info_t previous;
heap_block_info_t current;
heap_block_info_t next;
}heap_block_chain_t;


// Con-/Destructors
void* heap_block_init(heap_handle_t heap, heap_block_info_t const* info);


// Common
static inline size_t heap_block_calc_size(size_t size)
{
return align_up(size, sizeof(size_t))+2*sizeof(size_t);
}

static inline size_t heap_block_get_offset(void* ptr)
{
return (size_t)ptr-sizeof(size_t);
}

static inline void* heap_block_get_pointer(size_t offset)
{
return (void*)(offset+sizeof(size_t));
}


// Access
void heap_block_get_chain(heap_handle_t heap, void* ptr, heap_block_chain_t* info);
void heap_block_get_info(heap_handle_t heap, void* ptr, heap_block_info_t* info);


//===============
// Cluster-Group
//===============

typedef struct
{
union
	{
	struct
		{
		uint32_t dirty: 1;
		uint32_t locked: 1;
		uint32_t level: 14;
		uint32_t child_count: 16;
		};
	uint32_t value;
	};
}cluster_group_t;


// Con-/Destructors
static inline void cluster_group_init(cluster_group_t* group, uint16_t level, uint16_t child_count)
{
cluster_group_t set={ 0 };
set.level=level;
set.child_count=child_count;
group->value=set.value;
}


// Access
static inline uint16_t cluster_group_get_child_count(cluster_group_t* group)
{
cluster_group_t get;
get.value=group->value;
return (uint16_t)get.child_count;
}

size_t cluster_group_get_item_count(cluster_group_t* group);

static inline uint16_t cluster_group_get_level(cluster_group_t* group)
{
cluster_group_t get;
get.value=group->value;
return (uint16_t)get.level;
}

static inline bool cluster_group_is_dirty(cluster_group_t* group)
{
cluster_group_t get;
get.value=group->value;
return (uint16_t)get.dirty;
}

static inline bool cluster_group_is_locked(cluster_group_t* group)
{
cluster_group_t get;
get.value=group->value;
return (uint16_t)get.locked;
}


// Modification
static inline void cluster_group_set_child_count(cluster_group_t* group, uint16_t child_count)
{
cluster_group_t set;
set.value=group->value;
set.child_count=child_count;
group->value=set.value;
}

static inline void cluster_group_set_dirty(cluster_group_t* group, bool dirty)
{
cluster_group_t set;
set.value=group->value;
set.dirty=dirty;
group->value=set.value;
}

static inline void cluster_group_set_locked(cluster_group_t* group, bool lock)
{
cluster_group_t set;
set.value=group->value;
configASSERT((bool)set.locked!=lock);
set.locked=lock;
group->value=set.value;
}


//======================
// Cluster-Parent-Group
//======================

typedef struct
{
cluster_group_t header;
size_t item_count;
size_t first;
size_t last;
cluster_group_t* children[CLUSTER_GROUP_SIZE];
}cluster_parent_group_t;


// Access
uint16_t cluster_parent_group_get_group(cluster_parent_group_t* group, size_t* at);
int16_t cluster_parent_group_get_nearest_space(cluster_parent_group_t* group, int16_t pos);


// Modification
void cluster_parent_group_append_groups(cluster_parent_group_t* group, cluster_group_t* const* append, uint16_t count);
void cluster_parent_group_insert_groups(cluster_parent_group_t* group, uint16_t at, cluster_group_t* const* insert, uint16_t count);
void cluster_parent_group_remove_group(heap_handle_t heap, cluster_parent_group_t* group, uint16_t at);
void cluster_parent_group_remove_groups(cluster_parent_group_t* group, uint16_t at, uint16_t count);


//================
// Block-Map-Item
//================

typedef struct
{
size_t size;
union
	{
	struct
		{
		size_t offset: SIZE_BITS-1;
		size_t single: 1;
		};
	size_t entry;
	size_t index;
	};
}block_map_item_t;


//=================
// Block-Map-Group
//=================

typedef cluster_group_t block_map_group_t;

// Access
size_t block_map_group_get_first_size(block_map_group_t* group);
block_map_item_t* block_map_group_get_item(block_map_group_t* group, size_t size);
size_t block_map_group_get_last_size(block_map_group_t* group);

// Modification
bool block_map_group_add_block(heap_handle_t heap, block_map_group_t* group, heap_block_info_t const* info, bool again);
bool block_map_group_get_block(heap_handle_t heap, block_map_group_t* group, size_t min_size, heap_block_info_t* info);
bool block_map_group_remove_block(heap_handle_t heap, block_map_group_t* group, heap_block_info_t const* info);


//======================
// Block-Map-Item-Group
//======================

typedef struct
{
cluster_group_t header;
block_map_item_t items[CLUSTER_GROUP_SIZE];
}block_map_item_group_t;

// Con-/Destructors
block_map_item_group_t* block_map_item_group_create(heap_handle_t heap);

// Access
size_t block_map_item_group_get_first_size(block_map_item_group_t* group);
block_map_item_t* block_map_item_group_get_item(block_map_item_group_t* group, size_t size);
block_map_item_t* block_map_item_group_get_item_at(block_map_item_group_t* group, uint16_t at);
uint16_t block_map_item_group_get_item_pos(block_map_item_group_t* group, size_t size, bool* exists_ptr);
size_t block_map_item_group_get_last_size(block_map_item_group_t* group);

// Modification
bool block_map_item_group_add_block(heap_handle_t heap, block_map_item_group_t* group, heap_block_info_t const* info);
bool block_map_item_group_add_item(block_map_item_group_t* group, heap_block_info_t const* info, uint16_t pos);
void block_map_item_group_append_items(block_map_item_group_t* group, block_map_item_t const* items, uint16_t count);
void block_map_item_group_cleanup(block_map_item_group_t* group);
bool block_map_item_group_get_block(heap_handle_t heap, block_map_item_group_t* group, size_t min_size, heap_block_info_t* info, bool passive);
void block_map_item_group_insert_items(block_map_item_group_t* group, uint16_t pos, block_map_item_t const* items, uint16_t count);
bool block_map_item_group_remove_block(heap_handle_t heap, block_map_item_group_t* group, heap_block_info_t const* info);
size_t block_map_item_group_remove_item_at(block_map_item_group_t* group, size_t at, bool passive);
void block_map_item_group_remove_items(block_map_item_group_t* group, uint16_t at, uint16_t count);


//========================
// Block-Map-Parent-Group
//========================

typedef struct
{
cluster_group_t header;
size_t item_count;
size_t first_size;
size_t last_size;
block_map_group_t* children[CLUSTER_GROUP_SIZE];
}block_map_cluster_parent_group_t;

// Con-/Destructors
block_map_cluster_parent_group_t* block_map_cluster_parent_group_create(heap_handle_t heap, uint16_t level);
block_map_cluster_parent_group_t* block_map_cluster_parent_group_create_with_child(heap_handle_t heap, block_map_group_t* child);

// Access
block_map_item_t* block_map_cluster_parent_group_get_item(block_map_cluster_parent_group_t* group, size_t size);
uint16_t block_map_cluster_parent_group_get_item_pos(block_map_cluster_parent_group_t* group, size_t size, uint16_t* pos_ptr, bool must_exist);

// Modification
bool block_map_cluster_parent_group_add_block(heap_handle_t heap, block_map_cluster_parent_group_t* group, heap_block_info_t const* info, bool again);
bool block_map_cluster_parent_group_add_block_internal(heap_handle_t heap, block_map_cluster_parent_group_t* group, heap_block_info_t const* info, bool again);
void block_map_cluster_parent_group_append_groups(block_map_cluster_parent_group_t* group, block_map_group_t* const* append, uint16_t count);
bool block_map_cluster_parent_group_combine_child(heap_handle_t heap, block_map_cluster_parent_group_t* group, uint16_t pos);
void block_map_cluster_parent_group_combine_children(heap_handle_t heap, block_map_cluster_parent_group_t* group);
bool block_map_cluster_parent_group_get_block(heap_handle_t heap, block_map_cluster_parent_group_t* group, size_t min_size, heap_block_info_t* info, bool passive);
void block_map_cluster_parent_group_insert_groups(block_map_cluster_parent_group_t* group, uint16_t at, block_map_group_t* const* insert, uint16_t count);
void block_map_cluster_parent_group_move_children(block_map_cluster_parent_group_t* group, uint16_t from, uint16_t to, uint16_t count);
void block_map_cluster_parent_group_move_empty_slot(block_map_cluster_parent_group_t* group, uint16_t from, uint16_t to);
bool block_map_cluster_parent_group_remove_block(heap_handle_t heap, block_map_cluster_parent_group_t* group, heap_block_info_t const* info);
void block_map_cluster_parent_group_remove_groups(block_map_cluster_parent_group_t* group, uint16_t at, uint16_t count);
bool block_map_cluster_parent_group_shift_children(block_map_cluster_parent_group_t* group, uint16_t at, uint16_t count);
bool block_map_cluster_parent_group_split_child(heap_handle_t heap, block_map_cluster_parent_group_t* group, uint16_t at);
void block_map_cluster_parent_group_update_bounds(block_map_cluster_parent_group_t* group);


//===========
// Block-Map
//===========

typedef struct
{
block_map_group_t* root;
}block_map_t;

// Con-/Destructors
static inline void block_map_init(block_map_t* map)
{
map->root=NULL;
}

// Access
static inline size_t block_map_get_item_count(block_map_t* map)
{
if(map==NULL)
	return 0;
return cluster_group_get_item_count((cluster_group_t*)map->root);
}

static inline size_t block_map_get_last_size(block_map_t* map)
{
if(map==NULL)
	return 0;
return block_map_group_get_last_size(map->root);
}

// Modification
bool block_map_add_block(heap_handle_t heap, block_map_t* map, heap_block_info_t const* info);
bool block_map_drop_root(heap_handle_t heap, block_map_t* map);
bool block_map_get_block(heap_handle_t heap, block_map_t* map, size_t min_size, heap_block_info_t* info);
bool block_map_lift_root(heap_handle_t heap, block_map_t* map);
void block_map_remove_block(heap_handle_t heap, block_map_t* map, heap_block_info_t const* info);


//====================
// Offset-Index-Group
//====================

typedef cluster_group_t offset_index_group_t;

// Access
size_t offset_index_group_get_first_offset(offset_index_group_t* group);
size_t offset_index_group_get_last_offset(offset_index_group_t* group);

// Modification
bool offset_index_group_add_offset(heap_handle_t heap, offset_index_group_t* group, size_t offset, bool again);
void offset_index_group_remove_offset(heap_handle_t heap, offset_index_group_t* group, size_t offset);
size_t offset_index_group_remove_offset_at(heap_handle_t heap, offset_index_group_t* group, size_t at);


//=========================
// Offset-Index-Item-Group
//=========================

typedef struct offset_index_item_group_t
{
cluster_group_t header;
size_t items[CLUSTER_GROUP_SIZE];
}offset_index_item_group_t;

// Con-/Destructors
offset_index_item_group_t* offset_index_item_group_create(heap_handle_t heap);

// Access
size_t offset_index_item_group_get_first_offset(offset_index_item_group_t* group);
uint16_t offset_index_item_group_get_item_pos(offset_index_item_group_t* group, size_t offset, bool* exists_ptr);
size_t offset_index_item_group_get_last_offset(offset_index_item_group_t* group);

// Modification
bool offset_index_item_group_add_offset(offset_index_item_group_t* group, size_t offset);
void offset_index_item_group_append_items(offset_index_item_group_t* group, size_t const* items, uint16_t count);
void offset_index_item_group_insert_items(offset_index_item_group_t* group, uint16_t at, size_t const* insert, uint16_t count);
size_t offset_index_item_group_remove_item(offset_index_item_group_t* group, uint16_t at);
void offset_index_item_group_remove_offset(offset_index_item_group_t* group, size_t offset);
size_t offset_index_item_group_remove_offset_at(offset_index_item_group_t* group, size_t at, bool passive);
void offset_index_item_group_remove_items(offset_index_item_group_t* group, uint16_t at, uint16_t count);


//===========================
// Offset-Index-Parent-Group
//===========================

typedef struct
{
cluster_group_t header;
size_t item_count;
size_t first_offset;
size_t last_offset;
offset_index_group_t* children[CLUSTER_GROUP_SIZE];
}offset_index_cluster_parent_group_t;


// Con-/Destructors
offset_index_cluster_parent_group_t* offset_index_cluster_parent_group_create(heap_handle_t heap, uint16_t level);
offset_index_cluster_parent_group_t* offset_index_cluster_parent_group_create_with_child(heap_handle_t heap, offset_index_group_t* child);

// Access
uint16_t offset_index_cluster_parent_group_get_item_pos(offset_index_cluster_parent_group_t* group, size_t offset, uint16_t* pos_ptr, bool must_exist);

// Modification
bool offset_index_cluster_parent_group_add_offset(heap_handle_t heap, offset_index_cluster_parent_group_t* group, size_t offset, bool again);
bool offset_index_cluster_parent_group_add_offset_internal(heap_handle_t heap, offset_index_cluster_parent_group_t* group, size_t offset, bool again);
void offset_index_cluster_parent_group_append_groups(offset_index_cluster_parent_group_t* group, offset_index_group_t* const* append, uint16_t count);
bool offset_index_cluster_parent_group_combine_child(heap_handle_t heap, offset_index_cluster_parent_group_t* group, uint16_t at);
void offset_index_cluster_parent_group_combine_children(heap_handle_t heap, offset_index_cluster_parent_group_t* group);
void offset_index_cluster_parent_group_insert_groups(offset_index_cluster_parent_group_t* group, uint16_t at, offset_index_group_t* const* insert, uint16_t count);
void offset_index_cluster_parent_group_move_children(offset_index_cluster_parent_group_t* group, uint16_t from, uint16_t to, uint16_t count);
void offset_index_cluster_parent_group_move_empty_slot(offset_index_cluster_parent_group_t* group, uint16_t from, uint16_t to);
void offset_index_cluster_parent_group_remove_groups(offset_index_cluster_parent_group_t* group, uint16_t at, uint16_t count);
void offset_index_cluster_parent_group_remove_offset(heap_handle_t heap, offset_index_cluster_parent_group_t* group, size_t offset);
size_t offset_index_cluster_parent_group_remove_offset_at(heap_handle_t heap, offset_index_cluster_parent_group_t* group, size_t at, bool passive);
bool offset_index_cluster_parent_group_shift_children(offset_index_cluster_parent_group_t* group, uint16_t at, uint16_t count);
bool offset_index_cluster_parent_group_split_child(heap_handle_t heap, offset_index_cluster_parent_group_t* group, uint16_t at);
void offset_index_cluster_parent_group_update_bounds(offset_index_cluster_parent_group_t* group);


//==============
// Offset-Index
//==============

typedef struct
{
offset_index_group_t* root;
}offset_index_t;

// Con-/Destructors
void offset_index_init(offset_index_t* index);

// Access
inline size_t offset_index_get_offset_count(offset_index_t* index)
{
return cluster_group_get_item_count((cluster_group_t*)index->root);
}

// Modification
bool offset_index_add_offset(heap_handle_t heap, offset_index_t* index, size_t offset);
void offset_index_drop_root(heap_handle_t heap, offset_index_t* index);
bool offset_index_lift_root(heap_handle_t heap, offset_index_t* index);
void offset_index_remove_offset(heap_handle_t heap, offset_index_t* index, size_t offset);
size_t offset_index_remove_offset_at(heap_handle_t heap, offset_index_t* index, size_t at);


//==========
// Portable
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

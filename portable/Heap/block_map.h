//=============
// block_map.h
//=============

// Map to free memory-blocks sorted by size

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


#ifndef _BLOCK_MAP_H
#define _BLOCK_MAP_H


//=======
// Using
//=======

#include "cluster_group.h"
#include "heap_block.h"
#include "offset_index.h"


//======
// Item
//======

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
	offset_index_t index;
	};
}block_map_item_t;


//=======
// Group
//=======

typedef cluster_group_t block_map_group_t;

// Access
size_t block_map_group_get_first_size(block_map_group_t* group);
block_map_item_t* block_map_group_get_item(block_map_group_t* group, size_t size);
size_t block_map_group_get_last_size(block_map_group_t* group);

// Modification
bool block_map_group_add_block(heap_handle_t heap, block_map_group_t* group, heap_block_info_t const* info, bool again);
bool block_map_group_get_block(heap_handle_t heap, block_map_group_t* group, size_t min_size, heap_block_info_t* info);
bool block_map_group_remove_block(heap_handle_t heap, block_map_group_t* group, heap_block_info_t const* info);


//============
// Item-group
//============

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


//==============
// Parent-group
//==============

typedef struct
{
cluster_group_t header;
size_t item_count;
size_t first_size;
size_t last_size;
block_map_group_t* children[CLUSTER_GROUP_SIZE];
}block_map_parent_group_t;

// Con-/Destructors
block_map_parent_group_t* block_map_parent_group_create(heap_handle_t heap, uint16_t level);
block_map_parent_group_t* block_map_parent_group_create_with_child(heap_handle_t heap, block_map_group_t* child);

// Access
block_map_item_t* block_map_parent_group_get_item(block_map_parent_group_t* group, size_t size);
uint16_t block_map_parent_group_get_item_pos(block_map_parent_group_t* group, size_t size, uint16_t* pos_ptr, bool must_exist);

// Modification
bool block_map_parent_group_add_block(heap_handle_t heap, block_map_parent_group_t* group, heap_block_info_t const* info, bool again);
bool block_map_parent_group_add_block_internal(heap_handle_t heap, block_map_parent_group_t* group, heap_block_info_t const* info, bool again);
void block_map_parent_group_append_groups(block_map_parent_group_t* group, block_map_group_t* const* append, uint16_t count);
bool block_map_parent_group_combine_child(heap_handle_t heap, block_map_parent_group_t* group, uint16_t pos);
void block_map_parent_group_combine_children(heap_handle_t heap, block_map_parent_group_t* group);
bool block_map_parent_group_get_block(heap_handle_t heap, block_map_parent_group_t* group, size_t min_size, heap_block_info_t* info, bool passive);
void block_map_parent_group_insert_groups(block_map_parent_group_t* group, uint16_t at, block_map_group_t* const* insert, uint16_t count);
void block_map_parent_group_move_children(block_map_parent_group_t* group, uint16_t from, uint16_t to, uint16_t count);
void block_map_parent_group_move_empty_slot(block_map_parent_group_t* group, uint16_t from, uint16_t to);
bool block_map_parent_group_remove_block(heap_handle_t heap, block_map_parent_group_t* group, heap_block_info_t const* info);
void block_map_parent_group_remove_groups(block_map_parent_group_t* group, uint16_t at, uint16_t count);
bool block_map_parent_group_shift_children(block_map_parent_group_t* group, uint16_t at, uint16_t count);
bool block_map_parent_group_split_child(heap_handle_t heap, block_map_parent_group_t* group, uint16_t at);
void block_map_parent_group_update_bounds(block_map_parent_group_t* group);


//=====
// Map
//=====

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

#endif // _BLOCK_MAP_H

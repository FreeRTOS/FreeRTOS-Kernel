//================
// offset_index.h
//================

// Sorted offsets of free memory-blocks with the same size

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


#ifndef _OFFSET_INDEX_H
#define _OFFSET_INDEX_H


//=======
// Using
//=======

#include "cluster_group.h"


//=======
// Group
//=======

typedef cluster_group_t offset_index_group_t;

// Access
size_t offset_index_group_get_first_offset(offset_index_group_t* group);
size_t offset_index_group_get_last_offset(offset_index_group_t* group);

// Modification
bool offset_index_group_add_offset(heap_handle_t heap, offset_index_group_t* group, size_t offset, bool again);
void offset_index_group_remove_offset(heap_handle_t heap, offset_index_group_t* group, size_t offset);
size_t offset_index_group_remove_offset_at(heap_handle_t heap, offset_index_group_t* group, size_t at);


//============
// Item-group
//============

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


//==============
// Parent-group
//==============

typedef struct
{
cluster_group_t header;
size_t item_count;
size_t first_offset;
size_t last_offset;
offset_index_group_t* children[CLUSTER_GROUP_SIZE];
}offset_index_parent_group_t;


// Con-/Destructors
offset_index_parent_group_t* offset_index_parent_group_create(heap_handle_t heap, uint16_t level);
offset_index_parent_group_t* offset_index_parent_group_create_with_child(heap_handle_t heap, offset_index_group_t* child);

// Access
uint16_t offset_index_parent_group_get_item_pos(offset_index_parent_group_t* group, size_t offset, uint16_t* pos_ptr, bool must_exist);

// Modification
bool offset_index_parent_group_add_offset(heap_handle_t heap, offset_index_parent_group_t* group, size_t offset, bool again);
bool offset_index_parent_group_add_offset_internal(heap_handle_t heap, offset_index_parent_group_t* group, size_t offset, bool again);
void offset_index_parent_group_append_groups(offset_index_parent_group_t* group, offset_index_group_t* const* append, uint16_t count);
bool offset_index_parent_group_combine_child(heap_handle_t heap, offset_index_parent_group_t* group, uint16_t at);
void offset_index_parent_group_combine_children(heap_handle_t heap, offset_index_parent_group_t* group);
void offset_index_parent_group_insert_groups(offset_index_parent_group_t* group, uint16_t at, offset_index_group_t* const* insert, uint16_t count);
void offset_index_parent_group_move_children(offset_index_parent_group_t* group, uint16_t from, uint16_t to, uint16_t count);
void offset_index_parent_group_move_empty_slot(offset_index_parent_group_t* group, uint16_t from, uint16_t to);
void offset_index_parent_group_remove_groups(offset_index_parent_group_t* group, uint16_t at, uint16_t count);
void offset_index_parent_group_remove_offset(heap_handle_t heap, offset_index_parent_group_t* group, size_t offset);
size_t offset_index_parent_group_remove_offset_at(heap_handle_t heap, offset_index_parent_group_t* group, size_t at, bool passive);
bool offset_index_parent_group_shift_children(offset_index_parent_group_t* group, uint16_t at, uint16_t count);
bool offset_index_parent_group_split_child(heap_handle_t heap, offset_index_parent_group_t* group, uint16_t at);
void offset_index_parent_group_update_bounds(offset_index_parent_group_t* group);


//=======
// Index
//=======

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

#endif // _OFFSET_INDEX_H

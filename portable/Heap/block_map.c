//=============
// block_map.c
//=============

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


//=======
// Using
//=======

#include "heap_private.h"
#include "parent_group.h"


//=======
// Group
//=======


// Access

size_t block_map_group_get_first_size(block_map_group_t* group)
{
if(cluster_group_get_level(group)==0)
	return block_map_item_group_get_first_size((block_map_item_group_t*)group);
return ((block_map_parent_group_t*)group)->first_size;
}

block_map_item_t* block_map_group_get_item(block_map_group_t* group, size_t size)
{
if(cluster_group_get_level(group)==0)
	return block_map_item_group_get_item((block_map_item_group_t*)group, size);
return block_map_parent_group_get_item((block_map_parent_group_t*)group, size);
}

size_t block_map_group_get_last_size(block_map_group_t* group)
{
if(cluster_group_get_level(group)==0)
	return block_map_item_group_get_last_size((block_map_item_group_t*)group);
return ((block_map_parent_group_t*)group)->last_size;
}


// Modification

bool block_map_group_add_block(heap_handle_t heap, block_map_group_t* group, heap_block_info_t const* info, bool again)
{
cluster_group_set_locked((cluster_group_t*)group, true);
bool added=false;
if(cluster_group_get_level(group)==0)
	{
	added=block_map_item_group_add_block(heap, (block_map_item_group_t*)group, info);
	}
else
	{
	added=block_map_parent_group_add_block(heap, (block_map_parent_group_t*)group, info, again);
	}
cluster_group_set_locked((cluster_group_t*)group, false);
return added;
}

bool block_map_group_get_block(heap_handle_t heap, block_map_group_t* group, size_t min_size, heap_block_info_t* info)
{
bool passive=cluster_group_is_locked((cluster_group_t*)group);
if(cluster_group_get_level(group)==0)
	return block_map_item_group_get_block(heap, (block_map_item_group_t*)group, min_size, info, passive);
return block_map_parent_group_get_block(heap, (block_map_parent_group_t*)group, min_size, info, passive);
}

bool block_map_group_remove_block(heap_handle_t heap, block_map_group_t* group, heap_block_info_t const* info)
{
if(cluster_group_get_level(group)==0)
	return block_map_item_group_remove_block(heap, (block_map_item_group_t*)group, info);
return block_map_parent_group_remove_block(heap, (block_map_parent_group_t*)group, info);
}


//============
// Item-group
//============

// Con-/Destructors

block_map_item_group_t* block_map_item_group_create(heap_handle_t heap)
{
block_map_item_group_t* group=(block_map_item_group_t*)heap_alloc_internal(heap, sizeof(block_map_item_group_t));
if(group==NULL)
	return NULL;
cluster_group_init((cluster_group_t*)group, 0, 0);
return group;
}


// Access

size_t block_map_item_group_get_first_size(block_map_item_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==0)
	return 0;
return group->items[0].size;
}

block_map_item_t* block_map_item_group_get_item(block_map_item_group_t* group, size_t size)
{
bool exists=false;
int16_t pos=block_map_item_group_get_item_pos(group, size, &exists);
configASSERT(exists);
return &group->items[pos];
}

block_map_item_t* block_map_item_group_get_item_at(block_map_item_group_t* group, uint16_t at)
{
configASSERT(at<cluster_group_get_child_count((cluster_group_t*)group));
return &group->items[at];
}

uint16_t block_map_item_group_get_item_pos(block_map_item_group_t* group, size_t size, bool* exists_ptr)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t pos=0; pos<child_count; pos++)
	{
	block_map_item_t* item=&group->items[pos];
	if(item->entry==0)
		continue;
	if(item->size==size)
		{
		*exists_ptr=true;
		return pos;
		}
	if(item->size>size)
		return pos;
	}
return child_count;
}

size_t block_map_item_group_get_last_size(block_map_item_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==0)
	return 0;
return group->items[child_count-1].size;
}


// Modification

bool block_map_item_group_add_block(heap_handle_t heap, block_map_item_group_t* group, heap_block_info_t const* info)
{
bool exists=false;
uint16_t pos=block_map_item_group_get_item_pos(group, info->size, &exists);
if(!exists)
	return block_map_item_group_add_item(group, info, pos);
block_map_item_t* item=block_map_item_group_get_item_at(group, pos);
bool added=false;
if(item->single)
	{
	offset_index_t index;
	offset_index_init(&index);
	added=offset_index_add_offset(heap, &index, info->offset);
	if(!added)
		return false;
	if(item->offset)
		offset_index_add_offset(heap, &index, item->offset);
	item->index=index;
	}
else
	{
	added=offset_index_add_offset(heap, &item->index, info->offset);
	}
if(cluster_group_is_dirty((cluster_group_t*)group))
	{
	block_map_item_group_cleanup(group);
	cluster_group_set_dirty((cluster_group_t*)group, false);
	}
return added;
}

bool block_map_item_group_add_item(block_map_item_group_t* group, heap_block_info_t const* info, uint16_t at)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==CLUSTER_GROUP_SIZE)
	return false;
for(uint16_t u=child_count; u>at; u--)
	group->items[u]=group->items[u-1];
group->items[at].size=info->size;
group->items[at].offset=info->offset;
group->items[at].single=true;
cluster_group_set_child_count((cluster_group_t*)group, child_count+1);
return true;
}

void block_map_item_group_append_items(block_map_item_group_t* group, block_map_item_t const* items, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t u=0; u<count; u++)
	group->items[child_count+u]=items[u];
cluster_group_set_child_count((cluster_group_t*)group, child_count+count);
}

void block_map_item_group_cleanup(block_map_item_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t pos=0; pos<child_count; )
	{
	if(group->items[pos].offset==0)
		{
		for(uint16_t u=pos; u+1<child_count; u++)
			group->items[u]=group->items[u+1];
		child_count--;
		}
	else
		{
		pos++;
		}
	}
cluster_group_set_child_count((cluster_group_t*)group, child_count);
}

bool block_map_item_group_get_block(heap_handle_t heap, block_map_item_group_t* group, size_t min_size, heap_block_info_t* info, bool passive)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
bool exists=false;
uint16_t pos=block_map_item_group_get_item_pos(group, min_size, &exists);
if(pos==child_count)
	return false;
block_map_item_t* item=block_map_item_group_get_item_at(group, pos);
configASSERT(item->offset!=0);
info->size=item->size;
if(item->single)
	{
	info->offset=item->offset;
	block_map_item_group_remove_item_at(group, pos, passive);
	}
else
	{
	info->offset=offset_index_remove_offset_at(heap, &item->index, 0);
	if(!item->offset)
		block_map_item_group_remove_item_at(group, pos, passive);
	}
return true;
}

void block_map_item_group_insert_items(block_map_item_group_t* group, uint16_t pos, block_map_item_t const* items, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t u=child_count+count-1; u>=pos+count; u--)
	group->items[u]=group->items[u-count];
for(uint16_t u=0; u<count; u++)
	group->items[pos+u]=items[u];
cluster_group_set_child_count((cluster_group_t*)group, child_count+count);
}

bool block_map_item_group_remove_block(heap_handle_t heap, block_map_item_group_t* group, heap_block_info_t const* info)
{
bool exists=false;
uint16_t pos=block_map_item_group_get_item_pos(group, info->size, &exists);
configASSERT(exists);
block_map_item_t* item=block_map_item_group_get_item_at(group, pos);
if(item->single)
	{
	configASSERT(item->offset==info->offset);
	block_map_item_group_remove_item_at(group, pos, false);
	}
else
	{
	offset_index_remove_offset(heap, &item->index, info->offset);
	if(!item->offset)
		block_map_item_group_remove_item_at(group, pos, false);
	}
return true;
}

size_t block_map_item_group_remove_item_at(block_map_item_group_t* group, size_t at, bool passive)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
configASSERT(at<child_count);
uint16_t pos=(uint16_t)at;
size_t offset=group->items[pos].offset;
if(passive)
	{
	group->items[pos].entry=0;
	cluster_group_set_dirty((cluster_group_t*)group, true);
	}
else
	{
	for(uint16_t u=pos; u+1<child_count; u++)
		group->items[u]=group->items[u+1];
	cluster_group_set_child_count((cluster_group_t*)group, child_count-1);
	}
return offset;
}

void block_map_item_group_remove_items(block_map_item_group_t* group, uint16_t pos, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t u=pos; u+count<child_count; u++)
	group->items[u]=group->items[u+count];
cluster_group_set_child_count((cluster_group_t*)group, child_count-count);
}


//==============
// Parent-group
//==============

// Con-/Destructors

block_map_parent_group_t* block_map_parent_group_create(heap_handle_t heap, uint16_t level)
{
block_map_parent_group_t* group=(block_map_parent_group_t*)heap_alloc_internal(heap, sizeof(block_map_parent_group_t));
if(group==NULL)
	return NULL;
cluster_group_init((cluster_group_t*)group, level, 0);
group->first_size=0;
group->last_size=0;
group->item_count=0;
return group;
}

block_map_parent_group_t* block_map_parent_group_create_with_child(heap_handle_t heap, block_map_group_t* child)
{
block_map_parent_group_t* group=(block_map_parent_group_t*)heap_alloc_internal(heap, sizeof(block_map_parent_group_t));
if(group==NULL)
	return NULL;
uint16_t child_level=cluster_group_get_level((cluster_group_t*)child);
cluster_group_init((cluster_group_t*)group, child_level+1, 1);
group->first_size=block_map_group_get_first_size(child);
group->last_size=block_map_group_get_last_size(child);
group->item_count=cluster_group_get_item_count((cluster_group_t*)child);
group->children[0]=child;
return group;
}


// Access

block_map_item_t* block_map_parent_group_get_item(block_map_parent_group_t* group, size_t size)
{
uint16_t pos=0;
uint16_t count=block_map_parent_group_get_item_pos(group, size, &pos, true);
configASSERT(count>0);
return block_map_group_get_item(group->children[pos], size);
}

uint16_t block_map_parent_group_get_item_pos(block_map_parent_group_t* group, size_t size, uint16_t* pos_ptr, bool must_exist)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
uint16_t pos=0;
for(; pos<child_count; pos++)
	{
	size_t first_size=block_map_group_get_first_size(group->children[pos]);
	if(size<first_size)
		break;
	size_t last_size=block_map_group_get_last_size(group->children[pos]);
	if(size>last_size)
		continue;
	*pos_ptr=pos;
	return 1;
	}
if(must_exist)
	return 0;
if(child_count==1)
	pos=0;
if(pos==0)
	{
	*pos_ptr=pos;
	return 1;
	}
if(pos==child_count)
	{
	pos--;
	*pos_ptr=pos;
	return 1;
	}
pos--;
*pos_ptr=pos;
return 2;
}


// Modification

bool block_map_parent_group_add_block(heap_handle_t heap, block_map_parent_group_t* group, heap_block_info_t const* info, bool again)
{
if(!block_map_parent_group_add_block_internal(heap, group, info, again))
	return false;
group->item_count++;
block_map_parent_group_update_bounds(group);
if(cluster_group_is_dirty((cluster_group_t*)group))
	{
	block_map_parent_group_combine_children(heap, group);
	cluster_group_set_dirty((cluster_group_t*)group, false);
	}
return true;
}

bool block_map_parent_group_add_block_internal(heap_handle_t heap, block_map_parent_group_t* group, heap_block_info_t const* info, bool again)
{
uint16_t pos=0;
uint16_t count=block_map_parent_group_get_item_pos(group, info->size, &pos, false);
if(!again)
	{
	for(uint16_t u=0; u<count; u++)
		{
		if(block_map_group_add_block(heap, group->children[pos+u], info, false))
			return true;
		}
	if(block_map_parent_group_shift_children(group, pos, count))
		{
		count=block_map_parent_group_get_item_pos(group, info->size, &pos, false);
		for(uint16_t u=0; u<count; u++)
			{
			if(block_map_group_add_block(heap, group->children[pos+u], info, false))
				return true;
			}
		}
	}
if(!block_map_parent_group_split_child(heap, group, pos))
	return false;
count=block_map_parent_group_get_item_pos(group, info->size, &pos, false);
for(uint16_t u=0; u<count; u++)
	{
	if(block_map_group_add_block(heap, group->children[pos+u], info, true))
		return true;
	}
return false;
}

void block_map_parent_group_append_groups(block_map_parent_group_t* group, block_map_group_t* const* append, uint16_t count)
{
parent_group_append_groups((parent_group_t*)group, (cluster_group_t* const*)append, count);
block_map_parent_group_update_bounds(group);
}

bool block_map_parent_group_combine_child(heap_handle_t heap, block_map_parent_group_t* group, uint16_t pos)
{
uint16_t count=cluster_group_get_child_count(group->children[pos]);
if(count==0)
	{
	parent_group_remove_group(heap, (parent_group_t*)group, pos);
	return true;
	}
if(pos>0)
	{
	uint16_t before=cluster_group_get_child_count(group->children[pos-1]);
	if(count+before<=CLUSTER_GROUP_SIZE)
		{
		block_map_parent_group_move_children(group, pos, pos-1, count);
		parent_group_remove_group(heap, (parent_group_t*)group, pos);
		return true;
		}
	}
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(pos+1<child_count)
	{
	uint16_t after=cluster_group_get_child_count(group->children[pos+1]);
	if(count+after<=CLUSTER_GROUP_SIZE)
		{
		block_map_parent_group_move_children(group, pos+1, pos, after);
		parent_group_remove_group(heap, (parent_group_t*)group, pos+1);
		return true;
		}
	}
return false;
}

void block_map_parent_group_combine_children(heap_handle_t heap, block_map_parent_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t pos=0; pos<child_count; )
	{
	if(block_map_parent_group_combine_child(heap, group, pos))
		{
		child_count--;
		}
	else
		{
		pos++;
		}
	}
}

bool block_map_parent_group_get_block(heap_handle_t heap, block_map_parent_group_t* group, size_t min_size, heap_block_info_t* info, bool passive)
{
uint16_t pos=0;
uint16_t count=block_map_parent_group_get_item_pos(group, min_size, &pos, false);
configASSERT(count>0);
if(count==2)
	pos++;
if(!block_map_group_get_block(heap, group->children[pos], min_size, info))
	return false;
if(passive)
	{
	cluster_group_set_dirty((cluster_group_t*)group, true);
	}
else
	{
	block_map_parent_group_combine_child(heap, group, pos);
	}
group->item_count--;
block_map_parent_group_update_bounds(group);
return true;
}

void block_map_parent_group_insert_groups(block_map_parent_group_t* group, uint16_t at, block_map_group_t* const* insert, uint16_t count)
{
parent_group_insert_groups((parent_group_t*)group, at, (cluster_group_t* const*)insert, count);
block_map_parent_group_update_bounds(group);
}

void block_map_parent_group_move_children(block_map_parent_group_t* group, uint16_t from, uint16_t to, uint16_t count)
{
uint16_t level=cluster_group_get_level((cluster_group_t*)group);
if(level>1)
	{
	block_map_parent_group_t* src=(block_map_parent_group_t*)group->children[from];
	block_map_parent_group_t* dst=(block_map_parent_group_t*)group->children[to];
	if(from>to)
		{
		block_map_parent_group_append_groups(dst, src->children, count);
		block_map_parent_group_remove_groups(src, 0, count);
		}
	else
		{
		uint16_t src_count=cluster_group_get_child_count((cluster_group_t*)src);
		block_map_parent_group_insert_groups(dst, 0, &src->children[src_count-count], count);
		block_map_parent_group_remove_groups(src, src_count-count, count);
		}
	}
else
	{
	block_map_item_group_t* src=(block_map_item_group_t*)group->children[from];
	block_map_item_group_t* dst=(block_map_item_group_t*)group->children[to];
	if(from>to)
		{
		block_map_item_group_append_items(dst, src->items, count);
		block_map_item_group_remove_items(src, 0, count);
		}
	else
		{
		uint16_t src_count=cluster_group_get_child_count((cluster_group_t*)src);
		block_map_item_group_insert_items(dst, 0, &src->items[src_count-count], count);
		block_map_item_group_remove_items(src, src_count-count, count);
		}
	}
}

void block_map_parent_group_move_empty_slot(block_map_parent_group_t* group, uint16_t from, uint16_t to)
{
if(from<to)
	{
	for(uint16_t u=from; u<to; u++)
		block_map_parent_group_move_children(group, u+1, u, 1);
	}
else
	{
	for(uint16_t u=from; u>to; u--)
		block_map_parent_group_move_children(group, u-1, u, 1);
	}
}

bool block_map_parent_group_remove_block(heap_handle_t heap, block_map_parent_group_t* group, heap_block_info_t const* info)
{
uint16_t pos=0;
uint16_t count=block_map_parent_group_get_item_pos(group, info->size, &pos, true);
configASSERT(count==1);
if(block_map_group_remove_block(heap, group->children[pos], info))
	{
	group->item_count--;
	block_map_parent_group_combine_child(heap, group, pos);
	block_map_parent_group_update_bounds(group);
	return true;
	}
return false;
}

void block_map_parent_group_remove_groups(block_map_parent_group_t* group, uint16_t at, uint16_t count)
{
parent_group_remove_groups((parent_group_t*)group, at, count);
block_map_parent_group_update_bounds(group);
}

bool block_map_parent_group_shift_children(block_map_parent_group_t* group, uint16_t at, uint16_t count)
{
int16_t space=parent_group_get_nearest_space((parent_group_t*)group, at);
if(space<0)
	return false;
if(count>1&&space>at)
	at++;
block_map_parent_group_move_empty_slot(group, space, at);
return true;
}

bool block_map_parent_group_split_child(heap_handle_t heap, block_map_parent_group_t* group, uint16_t at)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==CLUSTER_GROUP_SIZE)
	return false;
block_map_group_t* child=NULL;
uint16_t level=cluster_group_get_level((cluster_group_t*)group);
if(level>1)
	{
	child=(block_map_group_t*)block_map_parent_group_create(heap, level-1);
	}
else
	{
	child=(block_map_group_t*)block_map_item_group_create(heap);
	}
if(!child)
	return false;
for(uint16_t u=child_count; u>at+1; u--)
	group->children[u]=group->children[u-1];
group->children[at+1]=child;
cluster_group_set_child_count((cluster_group_t*)group, child_count+1);
block_map_parent_group_move_children(group, at, at+1, 1);
return true;
}

void block_map_parent_group_update_bounds(block_map_parent_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==0)
	{
	group->first_size=0;
	group->last_size=0;
	return;
	}
for(uint16_t pos=0; pos<child_count; pos++)
	{
	group->first_size=block_map_group_get_first_size(group->children[pos]);
	if(group->first_size!=0)
		break;
	}
for(uint16_t pos=child_count; pos>0; pos--)
	{
	group->last_size=block_map_group_get_last_size(group->children[pos-1]);
	if(group->last_size!=0)
		break;
	}
}


//=====
// Map
//=====


// Modification

bool block_map_add_block(heap_handle_t heap, block_map_t* map, heap_block_info_t const* info)
{
heap_t* heap_ptr=(heap_t*)heap;
configASSERT(info->offset>=(size_t)heap+sizeof(heap_t));
configASSERT(info->offset<(size_t)heap+heap_ptr->used);
if(!map->root)
	{
	map->root=(block_map_group_t*)block_map_item_group_create(heap);
	if(!map->root)
		return false;
	}
if(block_map_group_add_block(heap, map->root, info, false))
	{
	block_map_drop_root(heap, map);
	return true;
	}
if(!block_map_lift_root(heap, map))
	return false;
if(!block_map_group_add_block(heap, map->root, info, true))
	return false;
block_map_drop_root(heap, map);
return true;
}

bool block_map_drop_root(heap_handle_t heap, block_map_t* map)
{
block_map_group_t* root=map->root;
if(cluster_group_is_locked((cluster_group_t*)root))
	return false;
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)root);
uint16_t level=cluster_group_get_level((cluster_group_t*)root);
if(level==0)
	return false;
if(child_count>1)
	return false;
block_map_parent_group_t* parent_group=(block_map_parent_group_t*)root;
map->root=parent_group->children[0];
heap_free_to_cache(heap, root);
return true;
}

bool block_map_get_block(heap_handle_t heap, block_map_t* map, size_t min_size, heap_block_info_t* info)
{
if(!map->root)
	return false;
if(block_map_group_get_block(heap, map->root, min_size, info))
	{
	block_map_drop_root(heap, map);
	return true;
	}
return false;
}

bool block_map_lift_root(heap_handle_t heap, block_map_t* map)
{
block_map_parent_group_t* root=block_map_parent_group_create_with_child(heap, map->root);
if(!root)
	return false;
map->root=(block_map_group_t*)root;
return true;
}

void block_map_remove_block(heap_handle_t heap, block_map_t* map, heap_block_info_t const* info)
{
if(block_map_group_remove_block(heap, map->root, info))
	block_map_drop_root(heap, map);
}

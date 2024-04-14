//================
// offset_index.c
//================

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


//=======
// Using
//=======

#include "heap.h"
#include "offset_index.h"
#include "parent_group.h"


//=======
// Group
//=======


// Access

size_t offset_index_group_get_first_offset(offset_index_group_t* group)
{
if(cluster_group_get_level(group)==0)
	return offset_index_item_group_get_first_offset((offset_index_item_group_t*)group);
return ((offset_index_parent_group_t*)group)->first_offset;
}

size_t offset_index_group_get_last_offset(offset_index_group_t* group)
{
if(cluster_group_get_level(group)==0)
	return offset_index_item_group_get_last_offset((offset_index_item_group_t*)group);
return ((offset_index_parent_group_t*)group)->last_offset;
}


// Modification

bool offset_index_group_add_offset(heap_handle_t heap, offset_index_group_t* group, size_t offset, bool again)
{
cluster_group_set_locked((cluster_group_t*)group, true);
bool added=false;
if(cluster_group_get_level(group)==0)
	{
	added=offset_index_item_group_add_offset((offset_index_item_group_t*)group, offset);
	}
else
	{
	added=offset_index_parent_group_add_offset(heap, (offset_index_parent_group_t*)group, offset, again);
	}
cluster_group_set_locked((cluster_group_t*)group, false);
return added;
}

void offset_index_group_remove_offset(heap_handle_t heap, offset_index_group_t* group, size_t offset)
{
if(cluster_group_get_level(group)==0)
	{
	offset_index_item_group_remove_offset((offset_index_item_group_t*)group, offset);
	}
else
	{
	offset_index_parent_group_remove_offset(heap, (offset_index_parent_group_t*)group, offset);
	}
}

size_t offset_index_group_remove_offset_at(heap_handle_t heap, offset_index_group_t* group, size_t at)
{
bool passive=cluster_group_is_locked((cluster_group_t*)group);
if(cluster_group_get_level(group)==0)
	return offset_index_item_group_remove_offset_at((offset_index_item_group_t*)group, at, passive);
return offset_index_parent_group_remove_offset_at(heap, (offset_index_parent_group_t*)group, at, passive);
}


//============
// Item-Group
//============


// Con-/Destructors

offset_index_item_group_t* offset_index_item_group_create(heap_handle_t heap)
{
offset_index_item_group_t* group=(offset_index_item_group_t*)heap_alloc_internal(heap, sizeof(offset_index_item_group_t));
if(group==NULL)
	return NULL;
cluster_group_init((cluster_group_t*)group, 0, 0);
return group;
}


// Access

size_t offset_index_item_group_get_first_offset(offset_index_item_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==0)
	return 0;
return group->items[0];
}

uint16_t offset_index_item_group_get_item_pos(offset_index_item_group_t* group, size_t offset, bool* exists_ptr)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t pos=0; pos<child_count; pos++)
	{
	size_t item=group->items[pos];
	if(item==offset)
		{
		*exists_ptr=true;
		return pos;
		}
	if(item>offset)
		return pos;
	}
return child_count;
}

size_t offset_index_item_group_get_last_offset(offset_index_item_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==0)
	return 0;
return group->items[child_count-1];
}


// Modification

bool offset_index_item_group_add_offset(offset_index_item_group_t* group, size_t offset)
{
bool exists=false;
uint16_t pos=offset_index_item_group_get_item_pos(group, offset, &exists);
configASSERT(!exists);
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==CLUSTER_GROUP_SIZE)
	return false;
for(uint16_t u=child_count; u>pos; u--)
	group->items[u]=group->items[u-1];
group->items[pos]=offset;
cluster_group_set_child_count((cluster_group_t*)group, child_count+1);
return true;
}

void offset_index_item_group_append_items(offset_index_item_group_t* group, size_t const* append, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
configASSERT(child_count+count<=CLUSTER_GROUP_SIZE);
for(uint16_t u=0; u<count; u++)
	group->items[child_count+u]=append[u];
cluster_group_set_child_count((cluster_group_t*)group, child_count+count);
}

void offset_index_item_group_insert_items(offset_index_item_group_t* group, uint16_t at, size_t const* insert, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t u=child_count+count-1; u>=at+count; u--)
	group->items[u]=group->items[u-count];
for(uint16_t u=0; u<count; u++)
	group->items[at+u]=insert[u];
cluster_group_set_child_count((cluster_group_t*)group, child_count+count);
}

size_t offset_index_item_group_remove_item(offset_index_item_group_t* group, uint16_t at)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
size_t offset=group->items[at];
for(uint16_t u=at; u+1<child_count; u++)
	group->items[u]=group->items[u+1];
cluster_group_set_child_count((cluster_group_t*)group, child_count-1);
return offset;
}

void offset_index_item_group_remove_offset(offset_index_item_group_t* group, size_t offset)
{
bool exists=false;
uint16_t pos=offset_index_item_group_get_item_pos(group, offset, &exists);
configASSERT(exists);
offset_index_item_group_remove_item(group, pos);
}

size_t offset_index_item_group_remove_offset_at(offset_index_item_group_t* group, size_t at, bool passive)
{
configASSERT(!passive);
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
configASSERT(at<child_count);
return offset_index_item_group_remove_item(group, (uint16_t)at);
}

void offset_index_item_group_remove_items(offset_index_item_group_t* group, uint16_t at, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
configASSERT(at+count<=child_count);
for(uint16_t u=at; u+count<child_count; u++)
	group->items[u]=group->items[u+count];
cluster_group_set_child_count((cluster_group_t*)group, child_count-count);
}


//==============
// Parent-group
//==============


// Con-/Destructors

offset_index_parent_group_t* offset_index_parent_group_create(heap_handle_t heap, uint16_t level)
{
offset_index_parent_group_t* group=(offset_index_parent_group_t*)heap_alloc_internal(heap, sizeof(offset_index_parent_group_t));
if(group==NULL)
	return NULL;
cluster_group_init((cluster_group_t*)group, level, 0);
group->first_offset=0;
group->last_offset=0;
group->item_count=0;
return group;
}

offset_index_parent_group_t* offset_index_parent_group_create_with_child(heap_handle_t heap, offset_index_group_t* child)
{
offset_index_parent_group_t* group=(offset_index_parent_group_t*)heap_alloc_internal(heap, sizeof(offset_index_parent_group_t));
if(group==NULL)
	return NULL;
uint16_t child_level=cluster_group_get_level(child);
cluster_group_init((cluster_group_t*)group, child_level+1, 1);
group->first_offset=offset_index_group_get_first_offset(child);
group->last_offset=offset_index_group_get_last_offset(child);
group->item_count=cluster_group_get_item_count((cluster_group_t*)child);
group->children[0]=child;
return group;
}


// Access

uint16_t offset_index_parent_group_get_item_pos(offset_index_parent_group_t* group, size_t offset, uint16_t* pos_ptr, bool must_exist)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
uint16_t pos=0;
for(; pos<child_count; pos++)
	{
	size_t first_offset=offset_index_group_get_first_offset(group->children[pos]);
	if(offset<first_offset)
		break;
	size_t last_offset=offset_index_group_get_last_offset(group->children[pos]);
	if(offset>last_offset)
		continue;
	*pos_ptr=pos;
	return 1;
	}
if(must_exist)
	return 0;
if(pos==0)
	{
	*pos_ptr=pos;
	return 1;
	}
if(pos==child_count)
	{
	*pos_ptr=pos-1;
	return 1;
	}
*pos_ptr=pos-1;
return 2;
}


// Modification

bool offset_index_parent_group_add_offset(heap_handle_t heap, offset_index_parent_group_t* group, size_t offset, bool again)
{
if(!offset_index_parent_group_add_offset_internal(heap, group, offset, again))
	return false;
group->item_count++;
offset_index_parent_group_update_bounds(group);
return true;
}

bool offset_index_parent_group_add_offset_internal(heap_handle_t heap, offset_index_parent_group_t* group, size_t offset, bool again)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(!child_count)
	return false;
uint16_t pos=0;
uint16_t count=offset_index_parent_group_get_item_pos(group, offset, &pos, false);
if(!again)
	{
	for(uint16_t u=0; u<count; u++)
		{
		if(offset_index_group_add_offset(heap, group->children[pos+u], offset, false))
			return true;
		}
	if(offset_index_parent_group_shift_children(group, pos, count))
		{
		count=offset_index_parent_group_get_item_pos(group, offset, &pos, false);
		for(uint16_t u=0; u<count; u++)
			{
			if(offset_index_group_add_offset(heap, group->children[pos+u], offset, false))
				return true;
			}
		}
	}
if(!offset_index_parent_group_split_child(heap, group, pos))
	return false;
count=offset_index_parent_group_get_item_pos(group, offset, &pos, false);
for(uint16_t u=0; u<count; u++)
	{
	if(offset_index_group_add_offset(heap, group->children[pos+u], offset, true))
		return true;
	}
return false;
}

void offset_index_parent_group_append_groups(offset_index_parent_group_t* group, offset_index_group_t* const* append, uint16_t count)
{
parent_group_append_groups((parent_group_t*)group, (cluster_group_t* const*)append, count);
offset_index_parent_group_update_bounds(group);
}

bool offset_index_parent_group_combine_child(heap_handle_t heap, offset_index_parent_group_t* group, uint16_t at)
{
uint16_t count=cluster_group_get_child_count((cluster_group_t*)group->children[at]);
if(count==0)
	{
	parent_group_remove_group(heap, (parent_group_t*)group, at);
	return true;
	}
if(at>0)
	{
	uint16_t before=cluster_group_get_child_count((cluster_group_t*)group->children[at-1]);
	if(count+before<=CLUSTER_GROUP_SIZE)
		{
		offset_index_parent_group_move_children(group, at, at-1, count);
		parent_group_remove_group(heap, (parent_group_t*)group, at);
		return true;
		}
	}
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(at+1<child_count)
	{
	uint16_t after=cluster_group_get_child_count((cluster_group_t*)group->children[at+1]);
	if(count+after<=CLUSTER_GROUP_SIZE)
		{
		offset_index_parent_group_move_children(group, at+1, at, after);
		parent_group_remove_group(heap, (parent_group_t*)group, at+1);
		return true;
		}
	}
return false;
}

void offset_index_parent_group_combine_children(heap_handle_t heap, offset_index_parent_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t pos=0; pos<child_count; )
	{
	if(offset_index_parent_group_combine_child(heap, group, pos))
		{
		child_count--;
		}
	else
		{
		pos++;
		}
	}
}

void offset_index_parent_group_insert_groups(offset_index_parent_group_t* group, uint16_t at, offset_index_group_t* const* insert, uint16_t count)
{
parent_group_insert_groups((parent_group_t*)group, at, (cluster_group_t* const*)insert, count);
offset_index_parent_group_update_bounds(group);
}

void offset_index_parent_group_move_children(offset_index_parent_group_t* group, uint16_t from, uint16_t to, uint16_t count)
{
uint16_t level=cluster_group_get_level((cluster_group_t*)group);
if(level>1)
	{
	offset_index_parent_group_t* src=(offset_index_parent_group_t*)group->children[from];
	offset_index_parent_group_t* dst=(offset_index_parent_group_t*)group->children[to];
	if(from>to)
		{
		offset_index_parent_group_append_groups(dst, src->children, count);
		offset_index_parent_group_remove_groups(src, 0, count);
		}
	else
		{
		uint16_t src_count=cluster_group_get_child_count((cluster_group_t*)src);
		offset_index_parent_group_insert_groups(dst, 0, &src->children[src_count-count], count);
		offset_index_parent_group_remove_groups(src, src_count-count, count);
		}
	}
else
	{
	offset_index_item_group_t* src=(offset_index_item_group_t*)group->children[from];
	offset_index_item_group_t* dst=(offset_index_item_group_t*)group->children[to];
	if(from>to)
		{
		offset_index_item_group_append_items(dst, src->items, count);
		offset_index_item_group_remove_items(src, 0, count);
		}
	else
		{
		uint16_t src_count=cluster_group_get_child_count((cluster_group_t*)src);
		offset_index_item_group_insert_items(dst, 0, &src->items[src_count-count], count);
		offset_index_item_group_remove_items(src, src_count-count, count);
		}
	}
}

void offset_index_parent_group_move_empty_slot(offset_index_parent_group_t* group, uint16_t from, uint16_t to)
{
if(from<to)
	{
	for(uint16_t u=from; u<to; u++)
		offset_index_parent_group_move_children(group, u+1, u, 1);
	}
else
	{
	for(uint16_t u=from; u>to; u--)
		offset_index_parent_group_move_children(group, u-1, u, 1);
	}
}

void offset_index_parent_group_remove_groups(offset_index_parent_group_t* group, uint16_t at, uint16_t count)
{
parent_group_remove_groups((parent_group_t*)group, at, count);
offset_index_parent_group_update_bounds(group);
}

void offset_index_parent_group_remove_offset(heap_handle_t heap, offset_index_parent_group_t* group, size_t offset)
{
uint16_t pos=0;
uint16_t count=offset_index_parent_group_get_item_pos(group, offset, &pos, true);
configASSERT(count==1);
offset_index_group_remove_offset(heap, group->children[pos], offset);
offset_index_parent_group_combine_child(heap, group, pos);
group->item_count--;
offset_index_parent_group_update_bounds(group);
}

size_t offset_index_parent_group_remove_offset_at(heap_handle_t heap, offset_index_parent_group_t* group, size_t at, bool passive)
{
uint16_t pos=parent_group_get_group((parent_group_t*)group, &at);
configASSERT(pos<CLUSTER_GROUP_SIZE);
size_t offset=offset_index_group_remove_offset_at(heap, group->children[pos], at);
if(passive)
	{
	cluster_group_set_dirty((cluster_group_t*)group, true);
	}
else
	{
	if(cluster_group_is_dirty((cluster_group_t*)group))
		{
		offset_index_parent_group_combine_children(heap, group);
		cluster_group_set_dirty((cluster_group_t*)group, false);
		}
	else
		{
		offset_index_parent_group_combine_child(heap, group, pos);
		}
	}
group->item_count--;
offset_index_parent_group_update_bounds(group);
return offset;
}

bool offset_index_parent_group_shift_children(offset_index_parent_group_t* group, uint16_t at, uint16_t count)
{
int16_t space=parent_group_get_nearest_space((parent_group_t*)group, at);
if(space<0)
	return false;
if(count>1&&space>at)
	at++;
offset_index_parent_group_move_empty_slot(group, space, at);
return true;
}

bool offset_index_parent_group_split_child(heap_handle_t heap, offset_index_parent_group_t* group, uint16_t at)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==CLUSTER_GROUP_SIZE)
	return false;
offset_index_group_t* child=NULL;
uint16_t level=cluster_group_get_level((cluster_group_t*)group);
if(level>1)
	{
	child=(offset_index_group_t*)offset_index_parent_group_create(heap, level-1);
	}
else
	{
	child=(offset_index_group_t*)offset_index_item_group_create(heap);
	}
if(!child)
	return false;
for(uint16_t u=child_count; u>at+1; u--)
	group->children[u]=group->children[u-1];
group->children[at+1]=child;
cluster_group_set_child_count((cluster_group_t*)group, child_count+1);
offset_index_parent_group_move_children(group, at, at+1, 1);
return true;
}

void offset_index_parent_group_update_bounds(offset_index_parent_group_t* group)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
if(child_count==0)
	{
	group->first_offset=0;
	group->last_offset=0;
	return;
	}
for(uint16_t pos=0; pos<child_count; pos++)
	{
	group->first_offset=offset_index_group_get_first_offset(group->children[pos]);
	if(group->first_offset!=0)
		break;
	}
for(uint16_t pos=child_count; pos>0; pos--)
	{
	group->last_offset=offset_index_group_get_last_offset(group->children[pos-1]);
	if(group->last_offset!=0)
		break;
	}
}


//=======
// Index
//=======

// Con-/Destructors

void offset_index_init(offset_index_t* index)
{
index->root=NULL;
}


// Modification

bool offset_index_add_offset(heap_handle_t heap, offset_index_t* index, size_t offset)
{
if(!index->root)
	{
	index->root=(offset_index_group_t*)offset_index_item_group_create(heap);
	if(!index->root)
		return false;
	}
if(offset_index_group_add_offset(heap, index->root, offset, false))
	return true;
if(!offset_index_lift_root(heap, index))
	return false;
return offset_index_group_add_offset(heap, index->root, offset, true);
}

void offset_index_drop_root(heap_handle_t heap, offset_index_t* index)
{
offset_index_group_t* root=index->root;
if(cluster_group_is_locked((cluster_group_t*)root))
	return;
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)root);
uint16_t level=cluster_group_get_level((cluster_group_t*)root);
if(level==0)
	{
	if(child_count==0)
		{
		index->root=NULL;
		heap_free_to_cache(heap, root);
		}
	return;
	}
if(child_count>1)
	return;
offset_index_parent_group_t* parent_group=(offset_index_parent_group_t*)root;
index->root=parent_group->children[0];
heap_free_to_cache(heap, root);
}

bool offset_index_lift_root(heap_handle_t heap, offset_index_t* index)
{
offset_index_parent_group_t* root=offset_index_parent_group_create_with_child(heap, index->root);
if(!root)
	return false;
index->root=(offset_index_group_t*)root;
return true;
}

void offset_index_remove_offset(heap_handle_t heap, offset_index_t* index, size_t offset)
{
offset_index_group_remove_offset(heap, index->root, offset);
offset_index_drop_root(heap, index);
}

size_t offset_index_remove_offset_at(heap_handle_t heap, offset_index_t* index, size_t at)
{
configASSERT(index->root);
size_t offset=offset_index_group_remove_offset_at(heap, index->root, at);
offset_index_drop_root(heap, index);
return offset;
}

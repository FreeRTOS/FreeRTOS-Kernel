//================
// parent_group.c
//================

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


//=======
// Using
//=======

#include "parent_group.h"


//========
// Access
//========

uint16_t parent_group_get_group(parent_group_t* group, size_t* pos)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
for(uint16_t u=0; u<child_count; u++)
	{
	size_t item_count=cluster_group_get_item_count(group->children[u]);
	if(*pos<item_count)
		return u;
	*pos-=item_count;
	}
return CLUSTER_GROUP_SIZE;
}

int16_t parent_group_get_nearest_space(parent_group_t* group, int16_t pos)
{
int16_t child_count=(int16_t)cluster_group_get_child_count((cluster_group_t*)group);
int16_t before=pos-1;
int16_t after=pos+1;
while(before>=0||after<child_count)
	{
	if(before>=0)
		{
		uint16_t count=cluster_group_get_child_count(group->children[before]);
		if(count<CLUSTER_GROUP_SIZE)
			return before;
		before--;
		}
	if(after<child_count)
		{
		uint16_t count=cluster_group_get_child_count(group->children[after]);
		if(count<CLUSTER_GROUP_SIZE)
			return after;
		after++;
		}
	}
return -1;
}


//==============
// Modification
//==============

void parent_group_append_groups(parent_group_t* group, cluster_group_t* const* append, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
configASSERT(child_count+count<=CLUSTER_GROUP_SIZE);
for(uint16_t u=0; u<count; u++)
	{
	group->children[child_count+u]=append[u];
	group->item_count+=cluster_group_get_item_count(append[u]);
	}
cluster_group_set_child_count((cluster_group_t*)group, child_count+count);
}

void parent_group_insert_groups(parent_group_t* group, uint16_t at, cluster_group_t* const* insert, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
configASSERT(at<=child_count);
configASSERT(child_count+count<=CLUSTER_GROUP_SIZE);
for(uint16_t u=child_count+count-1; u>=at+count; u--)
	group->children[u]=group->children[u-count];
for(uint16_t u=0; u<count; u++)
	{
	group->children[at+u]=insert[u];
	group->item_count+=cluster_group_get_item_count(insert[u]);
	}
cluster_group_set_child_count((cluster_group_t*)group, child_count+count);
}

void parent_group_remove_group(heap_handle_t heap, parent_group_t* group, uint16_t at)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
configASSERT(at<child_count);
cluster_group_t* child=group->children[at];
configASSERT(cluster_group_get_child_count(child)==0);
configASSERT(cluster_group_get_item_count(child)==0);
for(uint16_t u=at; u+1<child_count; u++)
	group->children[u]=group->children[u+1];
cluster_group_set_child_count((cluster_group_t*)group, child_count-1);
heap_free_to_cache(heap, child);
}

void parent_group_remove_groups(parent_group_t* group, uint16_t at, uint16_t count)
{
uint16_t child_count=cluster_group_get_child_count((cluster_group_t*)group);
configASSERT(at+count<=child_count);
for(uint16_t u=0; u<count; u++)
	group->item_count-=cluster_group_get_item_count(group->children[at+u]);
for(uint16_t u=at; u+count<child_count; u++)
	group->children[u]=group->children[u+count];
cluster_group_set_child_count((cluster_group_t*)group, child_count-count);
}

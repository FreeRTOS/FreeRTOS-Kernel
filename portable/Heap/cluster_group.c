//=================
// cluster_group.c
//=================

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


//=======
// Using
//=======

#include "cluster_group.h"
#include "parent_group.h"


//========
// Access
//========

size_t cluster_group_get_item_count(cluster_group_t* group)
{
if(!group)
	return 0;
cluster_group_t get;
get.value=group->value;
if(get.level==0)
	return get.child_count;
parent_group_t* parent_group=(parent_group_t*)group;
return parent_group->item_count;
}

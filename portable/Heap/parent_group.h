//================
// parent_group.h
//================

// Shared functions for block_map and offset_index.

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


#ifndef _PARENT_GROUP_H
#define _PARENT_GROUP_H


//=======
// Using
//=======

#include "cluster_group.h"


//==============
// Parent-Group
//==============

typedef struct
{
cluster_group_t header;
size_t item_count;
size_t first;
size_t last;
cluster_group_t* children[CLUSTER_GROUP_SIZE];
}parent_group_t;


//========
// Access
//========

uint16_t parent_group_get_group(parent_group_t* group, size_t* at);
int16_t parent_group_get_nearest_space(parent_group_t* group, int16_t pos);


//==============
// Modification
//==============

void parent_group_append_groups(parent_group_t* group, cluster_group_t* const* append, uint16_t count);
void parent_group_insert_groups(parent_group_t* group, uint16_t at, cluster_group_t* const* insert, uint16_t count);
void parent_group_remove_group(heap_handle_t heap, parent_group_t* group, uint16_t at);
void parent_group_remove_groups(parent_group_t* group, uint16_t at, uint16_t count);

#endif // _PARENT_GROUP_H

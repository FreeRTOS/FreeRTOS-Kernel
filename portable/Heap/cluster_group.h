//=================
// cluster_group.h
//=================

// Header of groups used for sorting.
// Memory-access needs to be 32 bit in IRAM.

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


#ifndef _CLUSTER_GROUP_H
#define _CLUSTER_GROUP_H


//=======
// Using
//=======

#include "heap.h"


//=======
// Group
//=======

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


//==================
// Con-/Destructors
//==================

static inline void cluster_group_init(cluster_group_t* group, uint16_t level, uint16_t child_count)
{
cluster_group_t set={ 0 };
set.level=level;
set.child_count=child_count;
group->value=set.value;
}


//========
// Access
//========

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


//==============
// Modification
//==============

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

#endif // _CLUSTER_GROUP_H

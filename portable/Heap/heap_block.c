//==============
// heap_block.c
//==============

// Copyright 2024, Sven Bieg (svenbieg@web.de)
// http://github.com/svenbieg/Heap


//=======
// Using
//=======

#include "heap.h"


//==================
// Con-/Destructors
//==================

void* heap_block_init(heap_handle_t heap, heap_block_info_t const* info)
{
heap_t* heap_ptr=(heap_t*)heap;
configASSERT(info->size%sizeof(size_t)==0);
configASSERT(info->offset>=(size_t)heap+sizeof(heap_t));
configASSERT(info->offset+info->size<=(size_t)heap+heap_ptr->size);
size_t* head_ptr=(size_t*)info->offset;
*head_ptr=info->header;
head_ptr++;
size_t* foot_ptr=(size_t*)(info->offset+info->size);
foot_ptr--;
*foot_ptr=info->header;
return head_ptr;
}


//========
// Access
//========

void heap_block_get_chain(heap_handle_t heap, void* ptr, heap_block_chain_t* info)
{
heap_t* heap_ptr=(heap_t*)heap;
size_t heap_offset=(size_t)heap;
size_t heap_start=heap_offset+sizeof(heap_t);
size_t offset=heap_block_get_offset(ptr);
size_t* head_ptr=(size_t*)offset;
info->current.offset=offset;
info->current.header=*head_ptr;
if(offset>heap_start)
	{
	size_t* foot_ptr=(size_t*)offset;
	foot_ptr--;
	info->previous.header=*foot_ptr;
	info->previous.offset=offset-info->previous.size;
	}
else
	{
	info->previous.header=0;
	info->previous.offset=0;
	}
size_t heap_end=heap_offset+heap_ptr->used;
size_t next_offset=offset+info->current.size;
if(next_offset<heap_end)
	{
	size_t* head_ptr=(size_t*)next_offset;
	info->next.offset=next_offset;
	info->next.header=*head_ptr;
	}
else
	{
	info->next.header=0;
	info->next.offset=0;
	}
}

void heap_block_get_info(heap_handle_t heap, void* ptr, heap_block_info_t* info)
{
heap_t* heap_ptr=(heap_t*)heap;
info->offset=heap_block_get_offset(ptr);
configASSERT(info->offset>=(size_t)heap+sizeof(heap_t));
configASSERT(info->offset<(size_t)heap+heap_ptr->used);
size_t* head_ptr=(size_t*)info->offset;
info->header=*head_ptr;
configASSERT(info->size>=3*sizeof(size_t));
configASSERT(info->offset+info->size<=(size_t)heap+heap_ptr->used);
configASSERT(*((size_t*)(info->offset+info->size-sizeof(size_t)))==*head_ptr);
}

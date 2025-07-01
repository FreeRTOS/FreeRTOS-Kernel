#ifndef FREERTOS_SKIP_LIST_H
#define FREERTOS_SKIP_LIST_H

#include <stdint.h>
#include <stddef.h>

#ifndef TickType_t
typedef unsigned int TickType_t;
#endif

#ifndef SKIP_LIST_MAX_LEVEL
#define SKIP_LIST_MAX_LEVEL 4 // Tunable for memory/complexity tradeoff
#endif

// Forward declaration
typedef struct SkipListNode {
    TickType_t key;
    void *value;
    struct SkipListNode *forward[SKIP_LIST_MAX_LEVEL];
} SkipListNode_t;

typedef struct SkipList {
    SkipListNode_t *header;
    int level;
} SkipList_t;

void vSkipListInit(SkipList_t *list);
void vSkipListInsert(SkipList_t *list, TickType_t key, void *value);
void vSkipListRemove(SkipList_t *list, TickType_t key);
void *pvSkipListSearch(SkipList_t *list, TickType_t key);

#endif // FREERTOS_SKIP_LIST_H

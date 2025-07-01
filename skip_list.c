#include "skip_list.h"
#include <stdlib.h>

static int xRandomLevel(void) {
    int level = 1;
    while ((rand() & 0x1) && level < SKIP_LIST_MAX_LEVEL)
        level++;
    return level;
}

void vSkipListInit(SkipList_t *list) {
    list->level = 1;
    list->header = (SkipListNode_t *)calloc(1, sizeof(SkipListNode_t));
    for (int i = 0; i < SKIP_LIST_MAX_LEVEL; i++)
        list->header->forward[i] = NULL;
}

void vSkipListInsert(SkipList_t *list, TickType_t key, void *value) {
    SkipListNode_t *update[SKIP_LIST_MAX_LEVEL];
    SkipListNode_t *x = list->header;
    for (int i = list->level - 1; i >= 0; i--) {
        while (x->forward[i] && x->forward[i]->key < key)
            x = x->forward[i];
        update[i] = x;
    }
    x = x->forward[0];
    if (x && x->key == key) {
        x->value = value;
        return;
    }
    int lvl = xRandomLevel();
    if (lvl > list->level) {
        for (int i = list->level; i < lvl; i++)
            update[i] = list->header;
        list->level = lvl;
    }
    x = (SkipListNode_t *)calloc(1, sizeof(SkipListNode_t));
    x->key = key;
    x->value = value;
    for (int i = 0; i < lvl; i++) {
        x->forward[i] = update[i]->forward[i];
        update[i]->forward[i] = x;
    }
}

void vSkipListRemove(SkipList_t *list, TickType_t key) {
    SkipListNode_t *update[SKIP_LIST_MAX_LEVEL];
    SkipListNode_t *x = list->header;
    for (int i = list->level - 1; i >= 0; i--) {
        while (x->forward[i] && x->forward[i]->key < key)
            x = x->forward[i];
        update[i] = x;
    }
    x = x->forward[0];
    if (x && x->key == key) {
        for (int i = 0; i < list->level; i++) {
            if (update[i]->forward[i] != x)
                break;
            update[i]->forward[i] = x->forward[i];
        }
        free(x);
        while (list->level > 1 && list->header->forward[list->level - 1] == NULL)
            list->level--;
    }
}

void *pvSkipListSearch(SkipList_t *list, TickType_t key) {
    SkipListNode_t *x = list->header;
    for (int i = list->level - 1; i >= 0; i--) {
        while (x->forward[i] && x->forward[i]->key < key)
            x = x->forward[i];
    }
    x = x->forward[0];
    if (x && x->key == key)
        return x->value;
    return NULL;
}

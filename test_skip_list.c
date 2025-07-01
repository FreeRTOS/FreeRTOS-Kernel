#include <stdio.h>
#include <stdlib.h>
#include "skip_list.h"

void print_skip_list(SkipList_t *list) {
    printf("Skip List: ");
    SkipListNode_t *node = list->header->forward[0];
    while (node) {
        printf("(%u, %p) ", node->key, node->value);
        node = node->forward[0];
    }
    printf("\n");
}

int main(void) {
    SkipList_t list;
    vSkipListInit(&list);

    // Insert test
    printf("Inserting values...\n");
    for (TickType_t i = 10; i > 0; --i) {
        int *val = (int *)malloc(sizeof(int));
        *val = i * 100;
        vSkipListInsert(&list, i, val);
    }
    print_skip_list(&list);

    // Search test
    printf("Searching for key 5...\n");
    int *found = (int *)pvSkipListSearch(&list, 5);
    if (found) {
        printf("Found key 5 with value %d\n", *found);
    } else {
        printf("Key 5 not found!\n");
    }

    printf("Searching for key 42...\n");
    found = (int *)pvSkipListSearch(&list, 42);
    if (found) {
        printf("Found key 42 with value %d\n", *found);
    } else {
        printf("Key 42 not found!\n");
    }

    // Remove test
    printf("Removing key 5...\n");
    vSkipListRemove(&list, 5);
    print_skip_list(&list);
    found = (int *)pvSkipListSearch(&list, 5);
    if (!found) {
        printf("Key 5 successfully removed.\n");
    }

    // Cleanup
    for (TickType_t i = 1; i <= 10; ++i) {
        int *val = (int *)pvSkipListSearch(&list, i);
        if (val) free(val);
    }
    // Free header node
    free(list.header);
    return 0;
}

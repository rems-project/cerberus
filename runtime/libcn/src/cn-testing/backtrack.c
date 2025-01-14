#include <string.h>

#include <cn-testing/backtrack.h>


static enum cn_gen_backtrack_request type = CN_GEN_BACKTRACK_NONE;

enum cn_gen_backtrack_request cn_gen_backtrack_type(void) {
    return type;
}

struct name_list {
    char* name;
    struct name_list* next;
};

static struct name_list* to_retry = NULL;
static size_t more_alloc_needed = 0;

void cn_gen_backtrack_reset(void) {
    type = CN_GEN_BACKTRACK_NONE;
    more_alloc_needed = 0;

    while (to_retry != NULL) {
        void* tmp = to_retry->next;
        free(to_retry);
        to_retry = tmp;
    }
}

void cn_gen_backtrack_assert_failure(void) {
    type = CN_GEN_BACKTRACK_ASSERT;
}

void cn_gen_backtrack_depth_exceeded() {
    type = CN_GEN_BACKTRACK_DEPTH;
}

void cn_gen_backtrack_relevant_add(char* varname) {
    struct name_list* new_node = (struct name_list*)malloc(sizeof(struct name_list));
    *new_node = (struct name_list){
        .name = varname, .next = 0
    };

    if (to_retry == NULL) {
        to_retry = new_node;
        return;
    }

    struct name_list* curr = to_retry;
    while (curr->next != NULL) {
        /* If variable is already in list, free `new_node` and return */
        if (strcmp(curr->name, varname) == 0) {
            free(new_node);
            return;
        }

        curr = curr->next;
    }

    /* Check last node */
    if (strcmp(curr->name, varname) == 0) {
        free(new_node);
        return;
    }

    curr->next = new_node;
}

void cn_gen_backtrack_relevant_add_many(char* toAdd[]) {
    for (int i = 0; toAdd[i] != NULL; i++) {
        cn_gen_backtrack_relevant_add(toAdd[i]);
    }
}

int cn_gen_backtrack_relevant_contains(char* varname) {
    struct name_list* curr = to_retry;
    while (curr != NULL) {
        if (strcmp(varname, curr->name) == 0) {
            return 1;
        }

        curr = curr->next;
    }
    return 0;
}

int cn_gen_backtrack_relevant_remap(char* from, char* to) {
    struct name_list* curr = to_retry;
    while (curr != NULL) {
        if (strcmp(from, curr->name) == 0) {
            curr->name = to;
            return 1;
        }

        curr = curr->next;
    }
    return 0;
}

int cn_gen_backtrack_relevant_remap_many(char* from[], char* to[]) {
    int number_of_remaps = 0;
    for (int i = 0; from[i] != 0; i++) {
        number_of_remaps += 1;
    }
    if (number_of_remaps == 0) {
        return 1;
    }

    char** toUnique = malloc(number_of_remaps * sizeof(char*));

    int successes = 1;
    for (int i = 0; from[i] != 0; i++) {
        // Get length of string
        size_t len = strlen(to[i]);

        // Copy the desired variable name
        toUnique[i] = (char*)malloc(len + 2);
        strcpy(toUnique[i], to[i]);

        // Give it an impossible name, but unique
        (toUnique[i][len]) = '$';
        (toUnique[i][len + 1]) = '\0';

        // We do this indirection in case there's a duplicate between `from` and `to`
        successes &= cn_gen_backtrack_relevant_remap(from[i], toUnique[i]);
    }

    for (int i = 0; from[i] != 0; i++) {
        successes &= cn_gen_backtrack_relevant_remap(toUnique[i], to[i]);
    }

    for (int i = 0; i < number_of_remaps; i++) {
        free(toUnique[i]);
    }
    free(toUnique);

    return successes;
}

void cn_gen_backtrack_alloc_set(size_t sz) {
    type = CN_GEN_BACKTRACK_ALLOC;

    more_alloc_needed = sz;
}

size_t cn_gen_backtrack_alloc_get() {
    return more_alloc_needed;
}

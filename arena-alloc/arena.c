/*
Credit: Chapter 6 (More Memory Management), C Interfaces and Implementations. David R Hanson. 
*/

#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <stdbool.h>
// #include <except.h>
#include "arena.h"

#define T Arena_T

// const Except_T Arena_NewFailed = { "Arena Creation Failed" };
// const Except_T Arena_Failed = { "Arena Allocation Failed" };

#define THRESHOLD 10

struct T {
    T prev;
    char *avail;
    char *limit;
};

union align {
    int i;
    long l;
    long *lp;
    void *p;
    void (*fp)(void);
    float f;
    double d;
    long double ld;
};

union header {
    struct T b;
    union align a;
};

static T freechunks;
static int nfree;

/* Create new empty arena */
T Arena_new(void) {
    T arena = malloc(sizeof (*arena));
    if (arena == NULL) {
        // RAISE(Arena_NewFailed);
        assert(false);
    }
    arena->prev = NULL;
    arena->limit = arena->avail = NULL;
    return arena;
}

/* Dellocate chunks in arena and then free arena itself */
void Arena_dispose(T *ap) {
    assert(ap && *ap);
    Arena_free(*ap);
    free(*ap);
    *ap = NULL;
}

void *Arena_alloc(T arena, long nbytes, const char *file, int line) {
    assert(arena);
    assert(nbytes > 0);

    /* Round up nbytes */
    nbytes = ((nbytes + sizeof (union align) - 1)/ (sizeof (union align)))*(sizeof (union align));

    /* Check if nbytes can be allocated inside remainder of current chunk */
    while (nbytes > arena->limit - arena->avail) {
        /* Allocate a new chunk */
        T ptr;
        char *limit;
        
        /* New chunk */
        if ((ptr = freechunks) != NULL) {
            freechunks = freechunks->prev;
            nfree--;
            limit = ptr->limit;
        } else {
            long m = sizeof(union header) + nbytes + 10*1024;
            ptr = malloc(m);

            /* Check if allocation failed */
            if (ptr == NULL) {
                assert(false);
                // (file = NULL) {
                //     RAISE(Arena_Failed);
                // }  else {
                //     Except_raise(&Arena_Failed, file, line);
                // }
            }

            limit = (char *)ptr + m;
        }

        *ptr = *arena;
        arena->avail = (char *)((union header *) ptr + 1);
        arena->limit = limit;
        arena->prev = ptr;
    }

    arena->avail += nbytes;
    return arena->avail - nbytes;
}

void *Arena_calloc(T arena, long count, long nbytes, const char *file, int line) {
    void *ptr;

    assert(count > 0);

    ptr = Arena_alloc(arena, count*nbytes, file, line);
    memset(ptr, '\0', count*nbytes);
    return ptr;
}

void Arena_free(T arena) {
    assert(arena);

    while (arena->prev) {
        struct T tmp = *arena->prev;
        
        if (nfree < THRESHOLD) {
            arena->prev->prev = freechunks;
            freechunks = arena->prev;
            nfree++;
            freechunks->limit = arena->limit;
        } else {
            free (arena->prev);
        }

        *arena = tmp;
    }

    assert(arena->limit == NULL);
    assert(arena->avail == NULL);
}
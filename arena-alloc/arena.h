/*
Credit: Chapter 6 (More Memory Management), C Interfaces and Implementations. David R Hanson. 
*/

// #ifndef ARENA_INCLUDED
// #define ARENA_INCLUDED
// #include <except.h>

#define T Arena_T
typedef struct T *T;

/* Arena exceptions */
// extern const Except_T Arena_NewFailed;
// extern const Except_T Arena_Failed;

/* Basic functions to create and destroy an arena */
extern T Arena_new(void);
extern void Arena_dispose(T *ap);

/* Arena allocation and freeing functions*/
extern void *Arena_alloc(T arena, long nbytes, const char *file, int line);
extern void *Arena_calloc(T arena, long count, long nbytes, const char *file, int line);
extern void Arena_free(T arena);




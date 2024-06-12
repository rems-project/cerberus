#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "alloc.h"

// #define foo(x)\
//     [ x ] = #x

// const char *kind_str[CNTYPE_SIZE] = {
//     foo(NODE_CN),
//     foo(SEQ),
//     foo(HASH_TABLE),
//     // HT_ENTRY,
//     foo(UNSIGNED_INT),
//     foo(CN_BOOL),
//     foo(CN_POINTER),
// };

static const signed int MEM_SIZE = 1024 * 1024 * 1024;
char buf[MEM_SIZE];
static void *curr = buf;

// 268,435,449

/* Allocation function */
// void *alloc_(long nbytes, const char *str) {
//     static unsigned long count[CNTYPE_SIZE];
//     void *res = curr;
//     if ((char *) (curr + nbytes) - buf > MEM_SIZE) {
//         printf("Out of memory!\n");
//         for (int i = 0; i < CNTYPE_SIZE; i++) {
//             printf("%s -> %lu\n", kind_str[i], count[i]);   
//         }
//         exit(1);
//     }
//     count[kind]++;
//     curr += nbytes;
//     return res;
// }

void *alloc_(long nbytes, const char *str, int line) {
    static unsigned long count;
    // printf("Alloc called: %s:%d\n", str, line);
    void *res = curr;
    if ((char *) (curr + nbytes) - buf > MEM_SIZE) {
        printf("Out of memory! %lu\n", count);
        exit(1);
    }
    count++;
    curr += nbytes;
    return res;
}


// void *alloc_zeros(long nbytes) {
//     void *res = alloc(nbytes);
//     bzero(res, nbytes);
//     return res;
// }


// int main(void) {
//     return 0;
// }

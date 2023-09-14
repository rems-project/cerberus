#include <stdio.h>
#include <string.h>


static const signed int MEM_SIZE = 10000;
char buf[MEM_SIZE];
static void *curr = buf;

/* Allocation function */
void *alloc(long nbytes) {
    void *res = curr;
    curr += nbytes;
    return res;
}

void *alloc_zeros(long nbytes) {
    void *res = alloc(nbytes);
    bzero(res, nbytes);
    return res;
}


// int main(void) {
//     return 0;
// }

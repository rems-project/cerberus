#include <stdio.h>

static const signed int MEM_SIZE = 10000;
char buf[MEM_SIZE];
static void *curr = buf;


void *alloc(long nbytes) {
    void *res = curr;
    curr += nbytes;
    return res;
}


int main(void) {
    return 0;
}

#include <inttypes.h>
#include <assert.h>
#include <stdio.h>

struct T {
};

struct S {
  int mem;
};

int main() {
    struct S y1;
    struct S y2;
    struct T x;
    struct S y3;
    assert (sizeof(x) == 0);
    uintptr_t y1_addr = (uintptr_t)&y1;
    uintptr_t y2_addr = (uintptr_t)&y2;
    uintptr_t x_addr = (uintptr_t)&x;
    uintptr_t y3_addr = (uintptr_t)&y3;
    printf("y1: %"PRIxPTR", y2: %"PRIxPTR", x: %"PRIxPTR", y3: %"PRIxPTR"\n", y1_addr, y2_addr, x_addr, y3_addr);
    return sizeof(x);
}

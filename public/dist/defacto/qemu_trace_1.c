#include <stdlib.h>
#include <stddef.h>
#include <inttypes.h>

typedef struct { char c; uint64_t u; } st;

uint64_t xg=5;

void f(uint64_t *pu) {
  *pu=9;
}
int main() {
  uint64_t xl=6;
  st s = {.c='A', .u=7 };
  uint64_t *pxg=&xg;
  f(pxg);
  uint64_t *pxl=&xl;
  f(pxl);
  st *ps = &s;
  uint64_t *psu=&(ps->u);
  f(psu);
  uint64_t *pm=(uint64_t*)malloc(sizeof(uint64_t));
  *pm=8;
  f(pm);
}

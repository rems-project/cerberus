#include <assert.h>
#include <stdio.h>
#include <inttypes.h>
char c[5];
int main() {
  char *cp = &(c[0]);
  assert(sizeof(uint32_t) == 4);
  uint32_t x0 = *((uint32_t *)cp);
  // does this have defined behaviour?
  uint32_t x1 = *((uint32_t *)(cp+4));
  printf("x0=%x  x1=%x\n",x0,x1);
}

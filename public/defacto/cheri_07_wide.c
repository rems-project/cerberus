#include <stdio.h>
#include <inttypes.h>
#include <limits.h>
#include <assert.h>
int x=1;
int main() {
  int *p = &x;
  uintptr_t i = (uintptr_t) p;
  assert( i <= UINT_MAX);
  unsigned int j = (unsigned int)i;
  uintptr_t k = (uintptr_t)j;
  int *q = (int *)k;
  *q = 2;
  printf("i=0x%"PRIxPTR" UINT_MAX=0x%x ULONG_MAX=0x%lx\n",
         i,UINT_MAX,ULONG_MAX);
  printf("x=%i  *q=%i\n",x,*q);
}

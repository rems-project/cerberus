#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
typedef struct { char c1; float f1; } st1;
typedef struct { char c2; float f2; } st2;
int main() {
  assert(sizeof(st1)==sizeof(st2));
  assert(offsetof(st1,c1)==offsetof(st2,c2));
  assert(offsetof(st1,f1)==offsetof(st2,f2));
  void *p = malloc(sizeof(st1)); assert (p != NULL);
  st1 *pst1 = (st1*)p;
  pst1->c1 = 'A';
  pst1->f1 = 1.0;
  float f = ((st2 *)p)->f2; // is this free of undefined behaviour?
  printf("f=%f\n",f);
}

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
typedef struct { char c1; float f1; } st1;
int main() {
  void *p = malloc(sizeof(st1)); assert (p != NULL);
  char *pc = (char*)((char*)p + offsetof(st1, c1));
  *pc = 'A';
  float *pf = (float *)((char*)p + offsetof(st1,f1));
  *pf = 1.0;
  st1 *pst1 = (st1 *)p;
  st1 s1;
  s1 = *pst1;   // is this free of undefined behaviour?
  printf("s1.c1=%c  s1.f1=%f\n", s1.c1, s1.f1);
}

#include <stdio.h>
#include <stdlib.h>
typedef struct { int  i1; } st1;
typedef struct { int  i2; } st2;
int main() {
  void *p = malloc(sizeof(st1));
  st1 *p1 = (st1 *)p;
  *p1 = (st1){.i1 = 1}; 
  st2 *p2 = (st2 *)p;
  int *pi = (int *)((char*)p + offsetof(st2,i1)); 
  int i = *pi;         // defined behaviour?
  printf("i=%i\n",i);
}

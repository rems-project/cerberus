#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main() {
  void *o = malloc(sizeof(int));
  *(int*)o = 1;
  void *p = malloc(sizeof(int));
  memcpy((void*)p, (const void*)o, sizeof(int));
  int *q = (int*)p;
  int j=*q;
  printf("j=%d\n",j);
}

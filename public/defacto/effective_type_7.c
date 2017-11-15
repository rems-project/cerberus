#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
typedef struct { char c1; float f1; } st1;
int main() {
  void *p = malloc(sizeof(st1)); assert (p != NULL);
  ((st1 *)p)->c1 = 'A';
  // is this free of undefined behaviour?
  float f = ((st1 *)p)->f1;
  printf("f=%f\n",f);
}

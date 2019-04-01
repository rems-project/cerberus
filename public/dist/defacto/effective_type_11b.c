#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <assert.h>
#include <stdint.h>

void f(void* p, void*q) {
  *(int *)p = 3;
  *(float *)p =3.14;
}

int main() {
  assert(sizeof(int32_t)==sizeof(float));
  void *p = malloc(sizeof(int32_t)); assert (p != NULL);
  f(p,p);
  int i=*(int*)p;
  printf("i=%d\n",i);
}

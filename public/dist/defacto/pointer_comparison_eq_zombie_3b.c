#include <stdlib.h>
#include <stdio.h>
extern int foo(void);
extern void bar(void* p) {
  free(p);
}

int main(void) {
  int n;
  n = foo();
  printf("n=%d\n",n);
}

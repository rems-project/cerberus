#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
struct X { int i; int j; };
int foo (struct X *p, struct X *q) {
  // does this have defined behaviour?
  q->j = 1;
  p->i = 0;
  return q->j;
}
int main() {
  assert(sizeof(struct X) == 2 * sizeof(int));
  unsigned char *p = malloc(3 * sizeof(int));
  printf("%i\n", foo ((struct X*)(p + sizeof(int)), 
                      (struct X*)p));
}

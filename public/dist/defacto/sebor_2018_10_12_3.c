#include <stdint.h>
#include <stdlib.h>
void f (int j) {
  int a[1] = { 0 }, b[1] = { 0 };
  int *p = a;
  intptr_t i = (intptr_t)p;
  i += j;
  p = (int*)i;
  if (p == &b[0])
    abort();
  *p = 123;
  if (b[0])
    abort();
}
int main() {
  f(sizeof(int));
}

#include <stdint.h>
#include <stdlib.h>
int a[3];
void f(void) {
  int *p = a;
  intptr_t i = (intptr_t)p;
  i += sizeof *p;
  p = (int*)i;
  if (p != &a[1])
    abort ();
}
int main() {
  f();
}

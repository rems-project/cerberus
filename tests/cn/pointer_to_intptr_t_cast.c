#include <inttypes.h>
void f() {
  int x=1;
  (intptr_t)&x;
  return;
}

int main(void) {
  f();
  return 0;
}
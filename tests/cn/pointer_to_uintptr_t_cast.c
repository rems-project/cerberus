#include <inttypes.h>
void f() {
  int x=1;
  (uintptr_t) &x;
  return;
}

int main(void) {
  f();
  return 0;
}
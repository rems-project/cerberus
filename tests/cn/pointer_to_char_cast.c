#include<inttypes.h>
void f() {
  int x=1;
  if ((128 <= (intptr_t)&x && (intptr_t) &x <= 255))
    (char)&x;
  return;
}
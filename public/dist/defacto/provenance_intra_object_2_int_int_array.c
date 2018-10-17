#include <stdlib.h>
typedef int T;
typedef int U;
struct S { T a[4]; U b[4]; } s;
void f(int i) {
  U u = s.b[0];
  s.a[i] = 0;
  if (u != s.b[0])   // can this be true in a valid program?
    abort ();
}
int main() {
  f(4);
}

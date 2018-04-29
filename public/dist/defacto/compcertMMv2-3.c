#include <stdio.h>
union point3d {
  struct { int x, y, z; } s;
  int d[3];
};
int main() {
  union point3d p;
  p.s.y = 42;
  int w;
  w = p.d[1];
  printf("w=%i\n",w);
}

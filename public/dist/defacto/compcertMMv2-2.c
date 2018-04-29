#include <stdio.h>
struct { int x, y, z; } s;
int main() {
  s.y = 41;
  ((int *) &s)[1] = 42;
  printf("s.y=%i ",s.y);
  *((int *) ((char *) &s + sizeof(int))) = 43;
  printf("s.y=%i\n",s.y);
}

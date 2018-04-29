#include <stdio.h>
typedef struct { int i1; int i2; } st;
int main() {
  st s1;
  s1.i1 = 1;
  st s2;
  s2 = s1; // does this have defined behaviour?
  printf("s2.i1=%i\n",s2.i1);
}

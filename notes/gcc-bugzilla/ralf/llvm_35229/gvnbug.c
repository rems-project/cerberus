#include <stdio.h>

int foo();

void test(int* gp1, int* gp2)
{
  int g = 0;
  int a = 0, b = 0;
  int y = 6666, x = 7777; // also try swapping these
  int* p = &g;
  int* q = &g;
  int* r = &g;

  if (foo()) {
    a = 1;
    p = &y+1;
    q = &x;
  }

  *gp1 = (int)p+1;
  if (q == p) {
    b = 1;
    *gp2 = (int)q+1;
    r = q;
  }
  *r = 42;

  printf("a = %d, b = %d, x = %d\n", a, b, x);
}

int main() {
  int gp1 = 0;
  int gp2 = 0;

  test(&gp1, &gp2);

  return 0;
}

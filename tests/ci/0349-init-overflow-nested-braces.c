#include <stdio.h>

// Excess initialisers are dropped (STD §6.7.9#2 makes them a constraint
// violation; we currently accept and ignore them). What matters here is that
// an excess *brace group* -- one that appears after the cursor has already
// run off the end of the object -- is dropped like any other excess
// initialiser, rather than being pushed back into the object or crashing the
// desugarer.

int a[2][2] = {{1, 2}, {3, 4}, {5, 6}};

// excess after an out-of-range designator
int b[2][2] = {[3] = {7, 8}, {9, 10}};

// an excess brace group following an excess scalar
struct S { int x[2]; int y; };
struct S s = {{1, 2}, 3, {4}};

int main(void)
{
  printf("a= {{%d, %d}, {%d, %d}}\n", a[0][0], a[0][1], a[1][0], a[1][1]);
  printf("b= {{%d, %d}, {%d, %d}}\n", b[0][0], b[0][1], b[1][0], b[1][1]);
  printf("s= {{%d, %d}, %d}\n", s.x[0], s.x[1], s.y);
}

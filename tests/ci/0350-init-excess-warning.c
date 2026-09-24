#include <stdio.h>

// STD §6.7.9#2: "No initializer shall attempt to provide a value for an
// object not contained within the entity being initialized." We accept these
// (as GCC and Clang do) but warn; --switches=strict_initialisers turns the
// warnings into constraint violations.
//
// The warnings go to stderr; this test checks that the values are dropped and
// that compilation still succeeds.

int arr[2] = {1, 2, 3};
int a2[5] = {[7] = 1};

struct S { int x; int y; };
struct S s = {1, 2, 3};

int main(void)
{
  printf("arr= {%d, %d}\n", arr[0], arr[1]);
  printf("a2= {%d, %d, %d, %d, %d}\n", a2[0], a2[1], a2[2], a2[3], a2[4]);
  printf("s= {%d, %d}\n", s.x, s.y);
}

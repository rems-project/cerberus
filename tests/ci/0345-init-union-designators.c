#include <stdio.h>

// STD §6.7.9#13: the initialiser of a union initialises the member named by
// the designator, or the first member when there is no designator.

struct T { int x; int y; };

union U { int a; double b; };
union V { int a; struct T s; };

// designating a member other than the first
union U designated = {.b = 1.5};

// re-designating: the last designator for the union wins
union U redesignated = {.a = 1, .b = 2.5};

// ... and the other way round
union U redesignated2 = {.b = 2.5, .a = 3};

// no designator: the first member
union U implicit = {9};

// a struct-typed member
union V structy = {.s = {4, 5}};

// a union nested in an array
union U arr[2] = {{.b = 6.5}, {.a = 7}};

// a union nested in a struct
struct W { int n; union U u; };
struct W w = {.n = 8, .u.b = 9.5};

int main(void)
{
  printf("designated= %d\n", designated.b == 1.5);
  printf("redesignated= %d\n", redesignated.b == 2.5);
  printf("redesignated2= %d\n", redesignated2.a == 3);
  printf("implicit= %d\n", implicit.a);
  printf("structy= {%d, %d}\n", structy.s.x, structy.s.y);
  printf("arr= {%d, %d}\n", arr[0].b == 6.5, arr[1].a);
  printf("w= {%d, %d}\n", w.n, w.u.b == 9.5);
}

#include <stdio.h>

// STD §6.7.2.1#13: the members of an anonymous struct/union are considered
// members of the containing structure, so a designator names them directly.

struct A {
  struct { int p; int q; };
  int r;
};

struct A designated = {.p = 1, .r = 3};
struct A elided = {1, 2, 3};

struct B {
  int n;
  union { int i; };
};

struct B b = {.n = 4, .i = 5};

int main(void)
{
  printf("designated= {{%d, %d}, %d}\n",
    designated.p, designated.q, designated.r);
  printf("elided= {{%d, %d}, %d}\n", elided.p, elided.q, elided.r);
  printf("b= {%d, {%d}}\n", b.n, b.i);
}

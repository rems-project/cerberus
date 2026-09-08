#include <stdio.h>

// STD §6.7.9#13: a member of an aggregate may be initialised by a single
// expression of compatible structure type -- here a compound literal, which
// must initialise the member rather than be pushed down into it by brace
// elision.
//
// These are block-scope objects: a compound literal is not a constant
// expression, so it cannot initialise an object of static storage duration
// (STD §6.7.9#4).

struct T { int a; int b; };
struct S { struct T t; int n; };

int main(void)
{
  struct S s = { (struct T){1, 2}, 3 };

  // a compound literal as an array element
  struct T ts[2] = { (struct T){4, 5}, (struct T){6, 7} };

  // reached by a designator
  struct S d = { .n = 8, .t = (struct T){9, 10} };

  printf("s= {{%d, %d}, %d}\n", s.t.a, s.t.b, s.n);
  printf("ts= {{%d, %d}, {%d, %d}}\n", ts[0].a, ts[0].b, ts[1].a, ts[1].b);
  printf("d= {{%d, %d}, %d}\n", d.t.a, d.t.b, d.n);
}

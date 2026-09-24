#include <stdio.h>

// STD §6.7.9#17: after a designator, initialisation continues forward from
// the designated element. STD §6.7.9#10: everything not initialised is zeroed.

struct T { int a; int b; int c; };

// a designator resets the current object; the next initialiser follows on
struct T t = {.b = 2, 3};

// designators into an array, out of order, with a gap
int a[5] = {[3] = 4, [1] = 2};

// designators on an array of unknown size: the size comes from the largest
// index reached, not from the number of initialisers
int unsized[] = {[4] = 5, 6};

// nested designators
struct U { struct T ts[2]; int n; };
struct U u = {.ts[1].b = 7, .n = 9};

int main(void)
{
  printf("t= {%d, %d, %d}\n", t.a, t.b, t.c);
  printf("a= {%d, %d, %d, %d, %d}\n", a[0], a[1], a[2], a[3], a[4]);
  printf("unsized[%lu]= {%d, %d, %d, %d, %d, %d}\n",
    sizeof(unsized)/sizeof(int),
    unsized[0], unsized[1], unsized[2], unsized[3], unsized[4], unsized[5]);
  printf("u= {{{%d, %d, %d}, {%d, %d, %d}}, %d}\n",
    u.ts[0].a, u.ts[0].b, u.ts[0].c,
    u.ts[1].a, u.ts[1].b, u.ts[1].c, u.n);
}

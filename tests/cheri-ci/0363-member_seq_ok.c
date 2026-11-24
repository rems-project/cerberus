// Companion of 0360-0362: these are all defined
struct s { int a; struct s *n; };
struct s g = {3, 0};
struct s *f(void) { g.a++; return &g; }

int main(void)
{
  struct s y = {2, 0}, x = {1, &y}, *p = &x;
  int i = 0, r = 0;
  struct s arr[2] = {{5, 0}, {6, 0}};
  r += arr[i++].a;       // i == 1, r == 5
  r += (arr + i++)->a;   // i == 2, r == 11
  r += (p = p->n)->a;    // p == &y, r == 13
  r += (x = y).a;        // x.a == 2, r == 15
  g.a = f()->a + 1;      // g.a == 5
  int *q = &arr[--i].a;  // i == 1
  return r + g.a + *q + i; // returns 27
}

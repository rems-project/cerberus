#include <stdlib.h>
struct S { char a[4], b[4]; } s[2];
void f (struct S *s, int i, int j) {
  char *p = &s[0].a[i];
  char *q = &s[1].a[j];
  char c = *p;
  *q = 0;
  if (c != *p)
    abort ();
}
int main() {
  f(s,4);
}

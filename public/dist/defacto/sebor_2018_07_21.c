#include <string.h>

struct S { char a[8]; void (*pf)(void); };

void f (struct S *p, const char *s) {
  char *q = (char*)p->a;
  strcpy (q, s);
}

int main() {
  struct S x; 
  f( &x, "foo");

  struct S y[2]; 
  f( &y, "foo");


}

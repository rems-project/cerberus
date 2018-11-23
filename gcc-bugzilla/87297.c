#include <string.h>

struct S { char a[4]; };

void g (struct S *p, const char *s)
{
  __builtin_strncpy (c->a, s, sizeof p->a);
}
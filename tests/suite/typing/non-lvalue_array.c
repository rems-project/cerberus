#ifndef __cerb__
#define __cerb_printtype(Z) Z
#endif

/* this is testing that non-lvalue array (like members of structs
   returned by a function) to not decay */
struct T {
  int a[2];
} s;

struct T f(void)
{
  return s;
}

int main(void)
{
  __cerb_printtype(s.a);   // should be int*
  __cerb_printtype(f().a); // should be int[2]
}


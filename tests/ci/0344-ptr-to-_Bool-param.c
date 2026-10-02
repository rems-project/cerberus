// The arguments of a call are converted "as if by assignment" to the types of the
// parameters (STD §6.5.2.2#7); for a pointer argument and a _Bool parameter this is the
// "compares equal to 0" test of §6.3.1.2#1, done with loaded_pointer_to_Bool() when the
// argument is elaborated. The inner_arg_temps calling convention used to convert that
// (already converted) value a second time, with loaded_ivfromfloat(), which is ill-typed.
#include <stdio.h>
#include <stddef.h>

int g(_Bool flag) { return flag; }
static int mid(int a, _Bool b, double d, int *p, _Bool c) { return a + b + (int)d + *p + c; }
static int var(_Bool b, ...) { return b; }

int main(void)
{
  int x = 4;
  int *p = &x;
  printf("%d %d %d %d %d %d %d %d\n",
         g((int*)0), g(NULL), g(p), g(&x), g((void*)&x),
         mid(1, &x, 3.0, &x, (int*)0), var(&x, 1), var((char*)0, 2));
  return 0;
}

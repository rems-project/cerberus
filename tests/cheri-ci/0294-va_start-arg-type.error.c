#include <stdarg.h>
void foo(int args, ...)
{
  va_list ap;
  int i;
  va_start (i, args);
}

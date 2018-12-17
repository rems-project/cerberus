#include "stdio.h"

int putchar(int c)
{
  return printf("%c", c);
}
int puts(const char *s)
{
  return printf("%s", s);
}

int fflush(FILE *stream)
{
  return 0;
}
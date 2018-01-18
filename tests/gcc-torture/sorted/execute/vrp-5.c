#include "cerberus.h"
/* { dg-require-effective-target int32plus } */

void test(unsigned int a, unsigned int b)
{
  if (a < 5)
    abort();
  if (b < 5)
    abort();
  if (a + b != 0U)
    abort();
}

int main(int argc, char *argv[])
{
  unsigned int x = 0x80000000;
  test(x, x);
  exit (0);
}




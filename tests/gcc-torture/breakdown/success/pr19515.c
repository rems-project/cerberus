#include "cerberus.h"
/* PR 19515 */

typedef union {
      char a2[8];
}aun;

int main(void)
{
  aun a = {{0}};

  if (a.a2[2] != 0)
    abort ();
  return 0;
}


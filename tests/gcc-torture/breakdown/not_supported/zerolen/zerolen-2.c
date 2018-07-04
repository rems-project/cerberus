#include "cerberus.h"
/* { dg-skip-if "assumes absence of larger-than-word padding" { epiphany-*-* } } */

typedef int word ;

struct foo
{
  word x;
  word y[0];
};

int 
main (void)
{
  if (sizeof(word) != sizeof(struct foo))
    abort();
  if (__alignof__(word) != __alignof__(struct foo))
    abort();
  return 0;
}

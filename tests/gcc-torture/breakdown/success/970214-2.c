#include "cerberus.h"
#define m(L) ('1' + (L))
int
main ()
{
  exit (m (0) != '1');
}

#include "cerberus.h"
/* PR 16348: Make sure that condition-first false loops DTRT.  */


int main()
{
  for (; 0 ;)
    {
      abort ();
    label:
      return 0;
    }
  goto label;
}

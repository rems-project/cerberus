#include "cerberus.h"
/* Origin: Joseph Myers <jsm28@cam.ac.uk>.

   This tests for inconsistency in whether wide STRING_CSTs use the host
   or the target endianness.  */


int
main (void)
{
  if ("a" "b"[1] != 'b')
    abort ();
  exit (0);
}

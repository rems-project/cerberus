#include "cerberus.h"
/* Assignments via pointers pointing to global variables were being killed
   by SSA-DCE.  Test contributed by Paul Brook <paul@nowt.org>  */

int glob; 
 
void 
fn2(int ** q) 
{ 
  *q = &glob; 
} 
 
void 
test (void) 
{ 
  int *p; 
 
  fn2(&p); 
 
  *p=42; 
} 
 
int 
main (void) 
{ 
  test(); 
  if (glob != 42) abort(); 
  exit (0); 
}

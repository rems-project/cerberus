#include "cerberus.h"
/* { dg-additional-options "-DSTACK_SIZE=[dg-effective-target-value stack_size]" { target { stack_size } } } */

#define STACK_REQUIREMENT (40000 * 4 + 256)
#if defined (STACK_SIZE) && STACK_SIZE < STACK_REQUIREMENT
int 
main (void) { exit (0); }
#else
int 
main (void){int d[40000];d[0]=0;exit(0);}
#endif

#include "cerberus.h"
/* { dg-options "-fwrapv" } */


int 
f (int j){return++j>0;}
int 
main (void){if(f((~0U)>>1))abort();exit(0);}

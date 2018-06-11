#include "cerberus.h"
void
f (int got){if(got!=0xffff)abort();}
int 
main (void){signed char c=-1;unsigned u=(unsigned short)c;f(u);exit(0);}

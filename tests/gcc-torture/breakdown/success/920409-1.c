#include "cerberus.h"
int 
x (void){signed char c=-1;return c<0;}int 
main (void){if(x()!=1)abort();exit(0);}

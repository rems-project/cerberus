#include "cerberus.h"
typedef int t;
int
f(t y){switch(y){case 1:return 1;}return 0;}
int 
main (void){if(f((t)1)!=1)abort();exit(0);}

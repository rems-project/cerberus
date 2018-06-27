#include "cerberus.h"
int x(const char*s){char a[1];const char*ss=s;a[*s++]|=1;return(int)ss+1==(int)s;}
int 
main (void){if(x("")!=1)abort();exit(0);}

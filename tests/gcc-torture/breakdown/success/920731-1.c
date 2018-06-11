#include "cerberus.h"
int 
f (int x){int i;for(i=0;i<8&&(x&1)==0;x>>=1,i++);return i;}
int 
main (void){if(f(4)!=2)abort();exit(0);}

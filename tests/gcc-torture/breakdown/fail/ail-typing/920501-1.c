#include "cerberus.h"
/* { dg-require-effective-target untyped_assembly } */
int s[2];
int 
x (void){if(!s[0]){s[1+s[1]]=s[1];return 1;}}
int 
main (void){s[0]=s[1]=0;if(x(0)!=1)abort();exit(0);}

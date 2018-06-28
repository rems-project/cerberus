#include "cerberus.h"
/* 920730-1.c */
int 
f1 (void)
{
	int b=INT_MIN;
	return b>=INT_MIN;
}

int 
f2 (void)
{
	int b=INT_MIN+1;
	return b>= (unsigned)(INT_MAX+2);
}

int 
f3 (void)
{
	int b=INT_MAX;
	return b>=INT_MAX;
}

int 
f4 (void)
{
	int b=-1;
	return b>=UINT_MAX;
}

int 
main (void)
{
	if((f1()&f2()&f3()&f4())!=1)
		abort();
		exit(0);
}

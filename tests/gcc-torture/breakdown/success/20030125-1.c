#include "cerberus.h"
/* Verify whether math functions are simplified.  */
/* { dg-require-effective-target c99_runtime } */
/* { dg-require-weak } */
double sin(double);
double floor(double);
float 
t(float a)
{
	return sin(a);
}
float 
q(float a)
{
	return floor(a);
}
double
q1(float a)
{
	return floor(a);
}
int 
main (void)
{
#ifdef __OPTIMIZE__
	if (t(0)!=0)
		abort ();
	if (q(0)!=0)
		abort ();
	if (q1(0)!=0)
		abort ();
#endif
	return 0;
}

double
floor(double a)
{
	abort ();
}

float
floorf(float a)
{
	return a;
}

double
sin(double a)
{
	return a;
}

float
sinf(float a)
{
	abort ();
}

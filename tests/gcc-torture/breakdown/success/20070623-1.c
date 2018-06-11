#include "cerberus.h"

int  nge(int a, int b) {return -(a >= b);}
int  ngt(int a, int b) {return -(a > b);}
int  nle(int a, int b) {return -(a <= b);}
int  nlt(int a, int b) {return -(a < b);}
int  neq(int a, int b) {return -(a == b);}
int  nne(int a, int b) {return -(a != b);}
int  ngeu(unsigned a, unsigned b) {return -(a >= b);}
int  ngtu(unsigned a, unsigned b) {return -(a > b);}
int  nleu(unsigned a, unsigned b) {return -(a <= b);}
int  nltu(unsigned a, unsigned b) {return -(a < b);}


int 
main (void)
{
  if (nge(INT_MIN, INT_MAX) !=  0) abort();
  if (nge(INT_MAX, INT_MIN) != -1) abort();
  if (ngt(INT_MIN, INT_MAX) !=  0) abort();
  if (ngt(INT_MAX, INT_MIN) != -1) abort();
  if (nle(INT_MIN, INT_MAX) != -1) abort();
  if (nle(INT_MAX, INT_MIN) !=  0) abort();
  if (nlt(INT_MIN, INT_MAX) != -1) abort();
  if (nlt(INT_MAX, INT_MIN) !=  0) abort();

  if (neq(INT_MIN, INT_MAX) !=  0) abort();
  if (neq(INT_MAX, INT_MIN) !=  0) abort();
  if (nne(INT_MIN, INT_MAX) != -1) abort();
  if (nne(INT_MAX, INT_MIN) != -1) abort();

  if (ngeu(0, ~0U) !=  0) abort();
  if (ngeu(~0U, 0) != -1) abort();
  if (ngtu(0, ~0U) !=  0) abort();
  if (ngtu(~0U, 0) != -1) abort();
  if (nleu(0, ~0U) != -1) abort();
  if (nleu(~0U, 0) !=  0) abort();
  if (nltu(0, ~0U) != -1) abort();
  if (nltu(~0U, 0) !=  0) abort();
  
  exit(0);
}

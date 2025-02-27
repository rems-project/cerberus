#include "libfile.h"

int foo(int i) 
{
  if (i == myval) return 0; 
  else return 1; 
}

int buz()
/*@ accesses myval; @*/
{
    return myval;
}

int main()
/*@ trusted; @*/
{
    buz();
    return 0;
}


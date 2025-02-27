#include "libfile.h" 

int bar() 
/*@ 
accesses myval; 
@*/
{ 
  myval = 1;
  return foo(1); 
}

int main()
/*@ trusted; @*/
{
    bar();
    return 0;
}

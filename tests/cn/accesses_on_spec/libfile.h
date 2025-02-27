int myval; 

int foo(int i); 
/*@
spec foo(i32 i);
accesses myval; 
requires myval == 1i32; 
         i == 1i32; 
ensures  return == 0i32; 
@*/

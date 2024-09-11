/*@ https://github.com/rems-project/cerberus/issues/551 @*/

int s; 
void a() 
/*@
  accesses s; 
@*/
{ 
  while ( 1 )  // Same bug with for(;;) 
  {
    ; 
  }
}

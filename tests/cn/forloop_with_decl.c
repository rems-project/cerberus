int for_with_decl() 
{
  int acc = 0; 
  for(int i = 0; i < 10; i++)
  /*@ inv 0i32 <= i; i <= 10i32;
          acc <= 10i32 @*/ 
  {
    acc = i; 
  }; 
  return acc;
}

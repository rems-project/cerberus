int ctz ()
/*@ ensures return == 0i32 @*/
{
  return __builtin_ctz(1);
}

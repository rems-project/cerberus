#define int_typ_20_30(x)  __builtin_choose_expr(__builtin_types_compatible_p(typeof(x),int), 20, 30)


int f (int x) 
/*@ ensures return == 20i32 @*/
{
  return int_typ_20_30(x);
}

int g (unsigned int x) 
/*@ ensures return == 30i32 @*/
{
  return int_typ_20_30(x);
}

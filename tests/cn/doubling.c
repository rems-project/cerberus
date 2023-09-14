
unsigned int
add_self (unsigned int x)
/*@ ensures return == x + x @*/
{
  return x + x;
}

unsigned int
add_self_twice (unsigned int x)
/*@ ensures return == x + x + x + x @*/
{
  unsigned int y = add_self(x);
  return y + y;
}





unsigned int
add_self (unsigned int x)
/*@ ensures return == x + x; @*/
{
  return x + x;
}

unsigned int
add_self_twice (unsigned int x)
/*@ ensures return == x * 4u32; @*/
{
  unsigned int y = add_self(x);
  return y + y;
}

int main(void)
/*@ trusted; @*/
{
  unsigned int r = add_self_twice(5);
}

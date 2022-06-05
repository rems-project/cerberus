void func(void)
{
  
}

int main(void)
{
  // making sure the elaboration deal with the fact the
  // first operand has type void
  return func(), 10;
}

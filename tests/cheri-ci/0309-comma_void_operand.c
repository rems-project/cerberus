void func(void)
{
  
}

int main(void)
{
  // making sure that the elaboration deals with
  // the fact that the first operand can have type void
  return func(), 10;
}

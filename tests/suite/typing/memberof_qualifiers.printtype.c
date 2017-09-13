// This is the example from STD §6.5.2.3#8
int main(void)
{
  struct T { int i; const int ci; };
  struct T s;
  const struct T cs;
  volatile struct T vs;
  
  __CERB_PRINT_TYPE(s.i);   // int
  __CERB_PRINT_TYPE(s.ci);  // const int
  __CERB_PRINT_TYPE(cs.i);  // const int
  __CERB_PRINT_TYPE(cs.ci); // const int
  __CERB_PRINT_TYPE(vs.i);  // volatile int
  __CERB_PRINT_TYPE(vs.ci); // volatile const int
}

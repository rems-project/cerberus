void foo(int const * p)
{
  p = 0; // Ok: p is a {} pointer to {const} int
}

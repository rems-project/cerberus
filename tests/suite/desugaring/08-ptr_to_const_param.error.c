void foo(int const * p)
{
  *p = 0; // Bad: p is a {} pointer to {const} int
}

void foo(int * const p)
{
  p = 0; // Bad: p is a {const} pointer to int
}

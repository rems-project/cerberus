// this test checks that the Ail typing ignores qualifiers when checking the compatiblity
// of pointer types of PTR vs PTR subtraction operator
int main(void)
{
  int x;
  int *p = &x;
  const int *q = &x;
  p - q;
  q - p;
}

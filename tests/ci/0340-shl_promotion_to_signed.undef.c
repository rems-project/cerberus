int main(void)
{
  unsigned int n = 1;
  unsigned char c = 1;
  n << 31; // defined (unsigned result type, so << has wrapping semantics)

  // the left operand 'c' has type 'unsigned char' which is promoted to
  // 'signed int', so the << operator has signed semantics.
  c << 30; // defined (signed result type, no overflow)
  c << 31; // UNDEFINED (signed result type, overflow!)
}

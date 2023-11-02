unsigned int sink;

int main(void)
{
  unsigned char  u1 = 0x7f;
  unsigned short u2 = 0x7fff;
  unsigned int   u3 = 0x7fffffff;
  signed char    s1 = 0x7f;
  signed short   s2 = 0x7fff;

  // DEFINED: u1 is unsigned so the result is wrapped around.
  // NOTE that the result type (promotion of the type of u1)
  // is signed int, but this is irrelevant.
  sink = u1 << 25;
  // DEFINED: the result is representable in signed int (but << 25 would be UB)
  sink = s1 << 24;
  
  // likewise all of these are DEFINED
  sink = u2 << 17;
  sink = s2 << 16;
  sink = u3 << 1;

  sink = u1 << 31;
  sink = u2 << 31;
  sink = u3 << 31;

  // see 0333-shift_non_representable.undef.c for the undefined cases
}

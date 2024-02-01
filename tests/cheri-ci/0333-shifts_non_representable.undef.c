unsigned int sink;

int main(void)
{
  signed char  s1 = 0x7f;
  signed short s2 = 0x7fff;

  // both DEFINED
  sink = s1 << 24;
  sink = s2 << 16;

  // both UNDEFINED (UB052b_non_representable_left_shift)
  sink = s1 << 25;
  sink = s2 << 17;
}
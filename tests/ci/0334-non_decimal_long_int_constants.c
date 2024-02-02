int main(void)
{
  int ret = 0;
  // all three large constants should have type: signed long
  ret |= (-1 < 8589934591) << 2;
  ret |= (-1 < 0x1FFFFFFFF) << 1;
  ret |= -1 < 0b111111111111111111111111111111111;
  return ret; // should return 7 (0b111)
}
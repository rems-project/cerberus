int main(void)
{
  int ret = 0;
  ret |= (-1 < 0x1FFFFFFFFFFFFFFF) << 3; // large constant has type: signed long
  ret |= (-1 < 0xFFFFFFFFFFFFFFFF) << 2; // large constant has type: unsigned long
  // large constant has type: signed long
  ret |= (-1 < 0b111111111111111111111111111111111111111111111111111111111111111) << 1;
  // large constant has type: unsigned long
  ret |= -1 < 0b1111111111111111111111111111111111111111111111111111111111111111;
  return ret; // should return 10 (0b1010)
}
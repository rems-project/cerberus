int main(void)
{
  return '\xFF' == -1; // in implementations where char has the same range as signed char, this returns 1
}

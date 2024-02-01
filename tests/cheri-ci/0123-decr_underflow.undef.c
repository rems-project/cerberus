#include <limits.h>
int main(void)
{
  int x = INT_MIN;
  signed char c = SCHAR_MIN;
  c--; // defined because of the promotion
  x--;
}

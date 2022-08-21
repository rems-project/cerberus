#include <limits.h>
int main(void)
{
  int x = INT_MAX;
  signed char c = SCHAR_MAX;
  c++; // defined because of the promotion
  x++;
}

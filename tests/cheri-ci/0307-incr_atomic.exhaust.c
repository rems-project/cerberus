// NOTE: this tests needs to be executed exhaustively to find a bug
#include <assert.h>
int x;

int f(void)
{
  return x++;
}

int main(void)
{
  // this checks that the increment is atomic with respect to the function call
  assert( 1 == (x++ + f()) );
}

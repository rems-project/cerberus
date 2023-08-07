/*
  STD §6.2.4 says that for an object with automatic storage duration declared
  with NO initializer, "the value becomes indeterminate each time the
  **declaration** is reached."
*/
int done = 0;
int printf(const char*, ...);
int main(void)
{
 l:
  ;
  int x; // here the value of x becomes indeterminate
  static int y;
  static int z;
  if (done) {
    // the value of x should be indeterminate
    // but the value of y
    // and the initialisation of z to zero
    // should have persisted
    printf("%d %d %d\n", x, y, z);
  } else {
    done = 1;
    x = 10;
    y = 20;
    goto l;
  }
}

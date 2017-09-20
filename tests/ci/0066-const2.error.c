volatile int * const x;

int main(void)
{
  *x = 0; // this is ok
  x = 0;  // this is an error
}

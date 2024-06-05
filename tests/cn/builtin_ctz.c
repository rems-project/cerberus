

int
f (unsigned int x)
{
  unsigned int y;

  if (x == 0) {
    x = 42;
  }

  y = __builtin_ctz(x);
  y = __builtin_ffs(y);

  if (y < 10) {
    return 1;
  }
  else {
    return 3;
  }
}


int main(void) {
  int r = f(5);
  return 0;
}
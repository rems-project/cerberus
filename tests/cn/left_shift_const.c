
#define BIT(n) (1UL << (n))

int
f (int x) {
  int mask = BIT(12 - 3) - 1;

  return 0;
}

int main(void) {
  int r = f(5);
  return 0;
}
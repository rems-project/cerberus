int fib (int n) {
  if (n <= 1) {
    return 1;
  } else {
    int x = fib (n - 2);
    int y = fib (n - 1);
    return x + y;
  }
}

int main (void) {
  if (fib (5) != 8) {
    return 1;
  } else {
    return 0;
  }
}

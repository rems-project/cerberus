int fib (int n) {
  if (n <= 1) {
    return 1;
  } else {
    return fib (n - 2) + fib (n - 1);
  }
}

int main (void) {
  if (fib (5) != 8) {
    return 1;
  } else {
    return 0;
  }
}

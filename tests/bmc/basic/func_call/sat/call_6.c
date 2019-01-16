int f(int x) {
  return x + 1;
}

int main(void) {
  int x = f(42);
  assert (x == 42);
  return 0;
}

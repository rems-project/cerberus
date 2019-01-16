int f(int x) {
  return x + 1;
}

int main(void) {
  int x = f(42);
  assert (x == 43);
  return 0;
}

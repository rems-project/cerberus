int f(void) {
  int x = 42;
  return x;
}

int main(void) {
  int x = f();
  assert (x != 42);
  return 0;
}

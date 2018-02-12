int x = 1;

void f(void) {
  if (x == 1) {
    x = x + 1;
  } else {
    x = 5;
  }
  assert (x == 2);
}

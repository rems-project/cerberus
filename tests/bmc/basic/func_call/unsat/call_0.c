int f(void) {
  return 1;
}

int main(void) {
  int ret = f();
  assert (ret == 1);
  return 0;
}

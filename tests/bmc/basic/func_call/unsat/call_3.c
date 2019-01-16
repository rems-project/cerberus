int f(void) {
  if (0) {
    42/0;
  }
  return 0;
}

int main(void) {
  f();
  return 0;
}

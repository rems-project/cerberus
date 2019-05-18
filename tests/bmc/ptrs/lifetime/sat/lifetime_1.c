int *f() {
  int z;
  return &z;
}

int main(void) {
  int *p = f();
  p - p;
}

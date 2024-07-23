void f() {
  int x=1;
  (unsigned int)&x;
  return;
}

int main(void) {
  f();
  return 0;
}
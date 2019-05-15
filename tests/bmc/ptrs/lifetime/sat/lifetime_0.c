int *f() {
  int x;
  return &x;
}
int main() {
  int *p = f();
  *p = 1;
}

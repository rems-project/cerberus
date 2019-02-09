int main() {
  int x = 1, y = 2;
  int *p = &x + 1;
  int *q = &y;
  __BMC_ASSUME(p == q && p != q);
}

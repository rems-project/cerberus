int main () {
  void *pv;
  int a = 1;
  int *pa = &a;
  return (pv = pa, 0);
}

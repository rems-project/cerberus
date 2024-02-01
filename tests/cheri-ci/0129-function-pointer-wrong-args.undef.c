int foo(int n) { return n; }
int goo() { return 666; }
int main() {
  int (*f)(int) = foo;
  int (*g)(void) = goo;
  void * p = (void*)f;
  g = (int (*)(void))p;
  return (*g)();
}

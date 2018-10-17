int foo(int n) { return n; }
int main() {
  int (*f)(int) = foo;
  void * p = (void*)f;
  f = (int (*)(int))p;
  return (*f)(42);
}

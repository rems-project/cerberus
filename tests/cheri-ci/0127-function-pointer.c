int foo(int n) { return n; }
int main() {
  int (*f)(int) = foo;
  return (*f)(42);
}

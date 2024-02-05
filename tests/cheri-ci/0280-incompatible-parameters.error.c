void foo(int * x);
int main() {
  struct { int x; } * a;
  foo(a);
}

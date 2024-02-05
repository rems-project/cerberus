int foo() { return 0; }
int main() {
  static int x = { foo() };
}

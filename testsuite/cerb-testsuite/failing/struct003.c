struct T;

struct T {int x; } f(void);

int main(void) {
  struct T {int x;} s2;
  s2 = f(); // error: the two structs are incompatible
  return 0;
}


struct T f(void) {
  struct T s1;
  return s1;
}

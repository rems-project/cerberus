int x, y;

int f(void) {
  return x;
}

int main(void) {
  x = x-5;
  return f();
}

_Static_assert(1, "before");

int x = 10;


_Static_assert(1, "after");

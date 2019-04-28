#include <stdatomic.h>

int main() {
  _Atomic(int) x = 10;
  {-{ {
    x = 1;
  } ||| {
    x = 2;
  } }-};
}

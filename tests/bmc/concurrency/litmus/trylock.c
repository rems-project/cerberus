// trylock
#include <threads.h>
int main() {
  mtx_t m;
  int r1, r2, r3;
  mtx_init(&m);
  {-{ {
    r1 = mtx_trylock(&m);
    if (r1 == thrd_success) {
      x = x + 1;
      x = x + 1
      mtx_unlock(&m);
    }
  } ||| {
    r2 = mtx_trylock(&m);
    if (r2 == thrd_success) {
      r3 = x;
      mtx_unlock(&m);
    } else {
      r3 = 3;
    }
  } }-};
  assert(!(r3 == 1));
  return r3;
}

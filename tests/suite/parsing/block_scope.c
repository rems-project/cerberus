/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T;
int x;
void f(void) {
  { T T;
    T = 1;
    typedef int x;
  }
  x = 1;
  T u;
}

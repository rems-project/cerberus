/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T;
void f(void) {
  T y = 1;
  if (1) {
    int T;
    T = 1;
  }
  T x = 1;
}

/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T, T1(T);

void f(void) {
  int (*T)(T x) = 0;
  int T1 = sizeof((int)T1);
}

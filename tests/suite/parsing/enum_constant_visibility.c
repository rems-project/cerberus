/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T;
void f(void) {
  int x;
  x = (enum {T, U = T+1})1 + T;
  int y = U - T;
}

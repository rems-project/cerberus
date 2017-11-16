/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int T, U, V;
int x;
int f(void) {
  x = sizeof(enum {T});
label: x = sizeof(enum {U});
  return sizeof(enum {V});
  x = T + U + V;
}

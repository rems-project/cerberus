/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef long T, U;
enum {V} (*f(T T, enum {U} y, int x[T+U]))(T t);
T x[(U)V+1];

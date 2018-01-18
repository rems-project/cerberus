/* Test from Jacques-Henri Jourdan and Francois Pottier TOPLAS 2017:
 * "A simple, possibly correct LR parser for C11"
 */
typedef int S, T, U;
struct S { int T; };
union U { int x; };
void f(void) {
  struct S s = { .T = 1 };
T: s.T = 2;
   union U u = { 1 };
   goto T;
   S ss = 1; T tt = 1; U uu = 1;
}

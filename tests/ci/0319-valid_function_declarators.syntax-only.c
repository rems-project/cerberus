// VALID: the two declarations of 'x' are in difference "function prototype scopes"
struct S {
  int (*f)(int x, int (*g)(int x));
};

// VALID: same a before
int fun1(void)
{
  return sizeof(int (*)(int x, int (*g)(int x)));
}
// VALID: same a before, PLUS "arg" is in scope of function body statement
int (*fun2(int arg, int x))(int x, int not_arg) {
  arg + x;
  return 0;
}

struct S {
  void* (*f)(struct S* s);
};
void* (*fun3(struct S *p))(struct S*){
  return p->f;
}

void (*fun4(int sig, void (*func)(int)))(int)
{
  return func;
}
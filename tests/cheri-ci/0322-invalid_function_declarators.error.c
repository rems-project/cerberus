int (*fun2(int arg, int x))(int x, int not_arg) {
  not_arg; // this is NOT in scope
}

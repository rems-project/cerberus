int ffs(int x)
/*@ ensures (x == 0i32) ? (return == 0i32) : true;
            (x == 1i32) ? (return == 1i32) : true;
            (x == 2i32) ? (return == 2i32) : true;
            (x == 3i32) ? (return == 1i32) : true;
            (x == 8i32) ? (return == 4i32) : true; @*/
{
  return __builtin_ffs(x);
}

int main(void) {
  int r = ffs(1);
  return 0;
}
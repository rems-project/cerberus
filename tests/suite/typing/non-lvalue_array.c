/* this is testing that non-lvalue array (like members of structs
   returned by a function) to not decay */
struct T {
  int a[2];
} s;

struct T f(void)
{
  return s;
}

int main(void)
{
  __CERB_PRINT_TYPE(s.a);   // should be int*
  __CERB_PRINT_TYPE(f().a); // should be int[2]
}


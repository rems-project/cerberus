struct T {
  int x;
};

int *p;

int main(void)
{
  _Atomic(struct T) st;
  p = &(st.x); // this is allowed
  *p; // this is undefined (§6.5.2.3#5)
}

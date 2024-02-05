struct T {
  int x;
};

int *p;
_Atomic(struct T) *st;

int main(void)
{
  p = &(st->x); // this is allowed
  *p; // this is undefined (§6.5.2.3#5)
}

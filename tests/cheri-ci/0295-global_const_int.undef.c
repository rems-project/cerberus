int x;
const int y;

int main(void)
{
  int *p = &x;
  int *q = (int *)&y;
  *p = 1; // this is ok
  *q = 1; // but this is UB
}

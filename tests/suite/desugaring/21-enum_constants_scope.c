typedef int T;

enum {A = 40, B};

int main(void)
{
  int ret = 0;
  {
    enum {C, A = 2};
    ret = A;
  }
  return ret + A; // should return 42
}

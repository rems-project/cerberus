int xs[2];
const int ys[2];

int main(void)
{
  xs[0] = 1; // this is ok
  ys[0] = 1; // but this is UB
}

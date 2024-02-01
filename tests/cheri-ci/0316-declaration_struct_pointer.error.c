struct T {
  int x;
};

struct T* func(void);

int main(void)
{
  struct T st = func();
}

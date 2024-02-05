int xxx = 0, yyy = 0;

int main(void)
{
  (xxx = 1, yyy = 0) + yyy; // RACE on y
}

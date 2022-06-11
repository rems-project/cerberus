int x, y;
int main(void)
{
  (x = 0, x = 0); // this tests that when pulling a negative action, its SB predecessor
                  // which happen to be negative are properly marked for exclusion
}

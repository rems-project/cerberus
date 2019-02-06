/* Not a data race, just assertion failure */

int main(void) {
  int x = 0;
  {-{ {
        assert (x == 0);
      }

  ||| {
        assert (x == 1);
      }
  }-};
}

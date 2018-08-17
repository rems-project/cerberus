int main(void) {
  int x = 0;
  {-{ {
        assert (x == 0 || x == 1);
      }

  ||| {
        assert (x == 0);
        x = 1;
      }
  }-};
  return 0;
}

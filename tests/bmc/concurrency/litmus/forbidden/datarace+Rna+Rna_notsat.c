int main(void) {
  int x = 0;
  {-{ {
        assert (x == 0);
      }

  ||| {
        assert (x == 0);
      }
  }-};
}

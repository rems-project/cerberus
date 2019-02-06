/*
 * Non-atomic load races with non-atomic write 
 */

int main(void) {
  int x = 0;
  int y;
  {-{ {
        y = (x == 3);
      }

  ||| {
        x = 3;
      }
  }-};

}

int x = 1, y = 1;

int main() {

  {-{ { 
        x = x + y;
        x = x + y;
        x = x + y;
      }
  ||| {
        y = y + x;
        y = y + x;
        y = y + x;
      }
  }-}
  assert (x <= 21 && y <= 21);
  return x;
}

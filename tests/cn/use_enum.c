

enum {
  num_x = 42,
  num_y = 0xdedbeef
};

unsigned int add_x_y (void)
/*@ ensures return == ((u32) (num_x + num_y)) @*/
{
  return num_x + num_y;
}


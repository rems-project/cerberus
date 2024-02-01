int glb;

void func(int x)
{
  glb = 200;
}

int main(void)
{
  func(glb = 100);
  return glb;
}
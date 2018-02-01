enum { A };

int main(void)
{
  // this is valid because the scope differs from the one where A was
  // previously declared
  enum { A };
}

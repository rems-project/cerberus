int main(void)
{
  char a[] = {sizeof(a), 0, 0}; // ERROR: glob has incomplete type
}

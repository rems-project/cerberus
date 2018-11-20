#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>

int main()
{
  return write (1, "TEST", 4);
}

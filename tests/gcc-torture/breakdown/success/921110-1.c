#include "cerberus.h"
typedef void (*frob)();
frob f[] = {abort};

int main(void)
{
  exit(0);
}

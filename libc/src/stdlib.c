#include "stdlib.h"

int abs(int i) 
{
  return i>=0 ? i : -i; 
}

// TODO: temporary hack
// TODO: if the string is too long, this is probably supposed to do something less stupid (at least not be UB :-)
int atoi(const char *nptr)
{
  int ret = 0;
  char c;
  
  while((c = *nptr++)) {
    if (c < '0' || '9' < c)
      break;
    ret = 10*ret + c - '0';
  }
  return ret;
}

// TODO: temporary hack
void *calloc(size_t nmemb, size_t size)
{
  unsigned char *ret;
  ret = malloc(nmemb * size);
  if (!ret)
    return ret;
  
  for (int i=0; i < nmemb*size; i++)
    ret[i] = 0;
  
  return ret;
}

// TODO: This is based on the standard
static unsigned long int __cerb_next = 1;
int rand(void)   // RAND_MAX assumed to be 32767
{
  __cerb_next = __cerb_next * 1103515245 + 12345;
  return (unsigned int)(__cerb_next/65536) % 32768;
}
void srand(unsigned int seed)
{
  __cerb_next = seed;
}



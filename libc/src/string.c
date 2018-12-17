#include "string.h"

char *strcpy (char * restrict s1, const char * restrict s2)
{
  char *res = s1;
  while ((*s1++ = *s2++));
  return (res);
}

char *strncpy (char * restrict s1, const char * restrict s2, size_t n)
{
  char *res = s1;
  while ((*s1++ = *s2++) && --n > 0)
    ;
  while (n && --n > 0)
    *s1++ = '\0';
  return (res);
}

void* memset(void *s, int c, size_t n)
{
  unsigned char *p = s;
  while (n--)
    *p++ = (unsigned char)c;
  return s;
}

int strcmp (const char *s1, const char *s2)
{
  while (*s1 && *s1 == *s2)
    s1++, s2++;
  return (*(unsigned char*)s1 - *(unsigned char*)s2);
}

int strncmp(const char *s1, const char *s2, size_t n)
{
  while ((*s1 && *s1 == *s2) && --n > 0)
    s1++, s2++;
  return (*s1 - *s2);
}

size_t strlen(const char *s)
{
  size_t len = 0;
  while(*s) len++, s++;
  return len;
}

char *strcat(char * restrict s1, const char * restrict s2)
{
  while(*s1++);
  s1--;
  while(*s2) *s1++ = *s2++;
  *s1 = '\0';
  return s1;
}

char *strchr(const char *s, int n)
{
  char c = (char) n;
  while (*s && (*s != c)) s++;
  if (*s || !c)
    return (char*)s;
  return NULL;
}

char *strrchr(const char *s, int n)
{
  char c = (char) n;
  char *p = (char*) s;
  while(*p++);
  p--;
  while ((p != (char*)s) && (*p != c)) --p;
  if (*p == c)
    return p;
  return NULL;
}

char* strdup(const char *s)
{
  void *malloc(size_t);
  size_t len = strlen(s)+1;
  char *sc = malloc(len);
  memcpy(sc, s, len);
  return sc;
}

// TODO:
char *strerror(int errnum)
{
  return "NOT IMPLEMENTED!";
}



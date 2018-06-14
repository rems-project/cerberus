#ifndef	_STRING_H_
#define	_STRING_H_

typedef __cerbty_size_t size_t;
#define NULL __cerbvar_NULL

void *memcpy(void * restrict s1, const void * restrict s2, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
void *memmove(void *s1, const void *s2, size_t n);
char *strcpy(char * restrict s1, const char * restrict s2);
char *strncpy(char * restrict s1, const char * restrict s2, size_t n);
char *strcat(char * restrict s1, const char * restrict s2);
char *strncat(char * restrict s1, const char * restrict s2, size_t n);
// int memcmp(const void *s1, const void *s2, size_t n);
int strcmp(const char *s1, const char *s2);
int strcoll(const char *s1, const char *s2);
int strncmp(const char *s1, const char *s2, size_t n);
size_t strxfrm(char * restrict s1, const char * restrict s2, size_t n);
void *memchr(const void *s, int c, size_t n);
char *strchr(const char *s, int c);
size_t strcspn(const char *s1, const char *s2);
char *strpbrk(const char *s1, const char *s2);
char *strrchr(const char *s, int c);
size_t strspn(const char *s1, const char *s2);
char *strstr(const char *s1, const char *s2);
char *strtok(char * restrict s1, const char * restrict s2);
void *memset(void *s, int c, size_t n);
char *strerror(int errnum);
size_t strlen(const char *s);

/*
#define __STDC_WANT_LIB_EXT1__ __cerb___STDC_WANT_LIB_EXT1__
typedef __cerb_errno_t errno_t;
typedef __cerb_rsize_t rsize_t;
errno_t memcpy_s(void * restrict s1, rsize_t s1max, const void * restrict s2, rsize_t n);
errno_t memmove_s(void *s1, rsize_t s1max, const void *s2, rsize_t n);
errno_t strcpy_s(char * restrict s1, rsize_t s1max, const char * restrict s2);
errno_t strncpy_s(char * restrict s1, rsize_t s1max, const char * restrict s2, rsize_t n);
errno_t strcat_s(char * restrict s1, rsize_t s1max, const char * restrict s2);
errno_t strncat_s(char * restrict s1, rsize_t s1max, const char * restrict s2, rsize_t n);
char *strtok_s(char * restrict s1, rsize_t * restrict s1max, const char * restrict s2, char ** restrict ptr);
errno_t memset_s(void *s, rsize_t smax, int c, rsize_t n);
errno_t strerror_s(char *s, rsize_t maxsize, errno_t errnum);
size_t strerrorlen_s(errno_t errnum);
size_t strnlen_s(const char *s, size_t maxsize);
*/



char *strcpy (char * restrict s1, const char * restrict s2)
{
  char *res = s1;
  while ((*s1++ = *s2++));
  return (res);
}

char *strncpy (char * restrict s1, const char * restrict s2, size_t n)
{
  char *res = s1;
  while ((*s1++ = *s2++) && --n > 0);
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
  return (*s1 - *s2);
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
  if (*s)
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

#else
#endif

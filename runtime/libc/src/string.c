#include <stdint.h>
#include <assert.h>
#include <stdlib.h>
#include "string.h"

#define MAX(a,b) ((a)>(b)?(a):(b))
#define MIN(a,b) ((a)<(b)?(a):(b))

#define BITOP(a,b,op) \
 ((a)[(size_t)(b)/(8*sizeof *(a))] op (size_t)1<<((size_t)(b)%(8*sizeof *(a))))

/***************************************************************************
 * 7.24.2 Copying functions
 ***************************************************************************/

void *memmove(void *dest, const void *src, size_t n)
{
  char *d = dest;
  const char *s = src;

  if (d==s) return d;
  if ((uintptr_t)s-(uintptr_t)d-n <= -2*n) return memcpy(d, s, n);

  if (d<s) {
    for (; n; n--) *d++ = *s++;
  } else {
    while (n) n--, d[n] = s[n];
  }

  return dest;
}

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

/***************************************************************************
 * 7.24.3 Concatenation functions
 ***************************************************************************/

char *strcat(char *restrict dest, const char *restrict src)
{
  strcpy(dest + strlen(dest), src);
  return dest;
}

char *strncat(char *restrict d, const char *restrict s, size_t n)
{
  char *a = d;
  d += strlen(d);
  while (n && *s) n--, *d++ = *s++;
  *d++ = 0;
  return a;
}

/***************************************************************************
 * 7.24.4 Comparison functions
 ***************************************************************************/

int strcmp (const char *s1, const char *s2)
{
  while (*s1 && *s1 == *s2)
    s1++, s2++;
  return (*(unsigned char*)s1 - *(unsigned char*)s2);
}

int strcoll(const char *l, const char *r)
{
  return strcmp(l, r);
}

int strncmp(const char *s1, const char *s2, size_t n)
{
  while ((*s1 && *s1 == *s2) && --n > 0)
    s1++, s2++;
  return (*s1 - *s2);
}

size_t strxfrm(char *restrict dest, const char *restrict src, size_t n)
{
  size_t l = strlen(src);
  if (n > l) strcpy(dest, src);
  return l;
}

/***************************************************************************
 * 7.24.5 Search functions
 ***************************************************************************/

void *memchr(const void *src, int c, size_t n)
{
  const unsigned char *s = src;
  c = (unsigned char)c;
  for (; n && *s != c; s++, n--);
  return n ? (void *)s : (void*)0;
}

char *strchr(const char *s, int n)
{
  char c = (char) n;
  while (*s && (*s != c)) s++;
  if (*s || !c)
    return (char*)s;
  return NULL;
}

size_t strcspn(const char *s, const char *c)
{
  const char *a = s;
  size_t byteset[32/sizeof(size_t)];

  if (!c[0] || !c[1]) return strchrnul(s, *c)-(char*)a;

  memset(byteset, 0, sizeof byteset);
  do {
    if (!BITOP(byteset, *(unsigned char *)c, |=))
      break;
    c++;
  } while (*c);
  do {
    if (BITOP(byteset, *(unsigned char *)s, &))
      break;
    s++;
  } while (*s);
  return s-a;
}

char *strpbrk(const char *s, const char *b)
{
  s += strcspn(s, b);
  return *s ? (char *)s : (char*)0;
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

size_t strspn(const char *s, const char *c)
{
  const char *a = s;
  size_t byteset[32/sizeof(size_t)] = { 0 };

  if (!c[0]) return 0;
  if (!c[1]) {
    for (; *s == *c; s++);
    return s-a;
  }

  for (; *c && BITOP(byteset, *(unsigned char *)c, |=); c++);
  for (; *s && BITOP(byteset, *(unsigned char *)s, &); s++);
  return s-a;
}

static char *twobyte_strstr(const unsigned char *h, const unsigned char *n)
{
  uint16_t nw = n[0]<<8 | n[1], hw = h[0]<<8 | h[1];
  for (h++; *h && hw != nw; hw = hw<<8 | *++h);
  return *h ? (char *)h-1 : (char*)0;
}

static char *threebyte_strstr(const unsigned char *h, const unsigned char *n)
{
  uint32_t nw = n[0]<<24 | n[1]<<16 | n[2]<<8;
  uint32_t hw = h[0]<<24 | h[1]<<16 | h[2]<<8;
  for (h+=2; *h && hw != nw; hw = (hw|*++h)<<8);
  return *h ? (char *)h-2 : (char*)0;
}

static char *fourbyte_strstr(const unsigned char *h, const unsigned char *n)
{
  uint32_t nw = n[0]<<24 | n[1]<<16 | n[2]<<8 | n[3];
  uint32_t hw = h[0]<<24 | h[1]<<16 | h[2]<<8 | h[3];
  for (h+=3; *h && hw != nw; hw = hw<<8 | *++h);
  return *h ? (char *)h-3 : (char*)0;
}

static char *strtok_p;
char *strtok(char *restrict s, const char *restrict sep)
{
  if (!s && !(s = strtok_p)) return NULL;
  s += strspn(s, sep);
  if (!*s) return strtok_p = 0;
  strtok_p = s + strcspn(s, sep);
  if (*strtok_p) *strtok_p++ = 0;
  else strtok_p = 0;
  return s;
}

static char *twoway_strstr(const unsigned char *h, const unsigned char *n)
{
  const unsigned char *z;
  size_t l, ip, jp, k, p, ms, p0, mem, mem0;
  size_t byteset[32 / sizeof(size_t)] = { 0 };
  size_t shift[256];

  /* Computing length of needle and fill shift table */
  for (l=0; n[l] && h[l]; l++)
    BITOP(byteset, n[l], |=), shift[n[l]] = l+1;
  if (n[l]) return 0; /* hit the end of h */

  /* Compute maximal suffix */
  ip = -1; jp = 0; k = p = 1;
  while (jp+k<l) {
    if (n[ip+k] == n[jp+k]) {
      if (k == p) {
        jp += p;
        k = 1;
      } else k++;
    } else if (n[ip+k] > n[jp+k]) {
      jp += k;
      k = 1;
      p = jp - ip;
    } else {
      ip = jp++;
      k = p = 1;
    }
  }
  ms = ip;
  p0 = p;

  /* And with the opposite comparison */
  ip = -1; jp = 0; k = p = 1;
  while (jp+k<l) {
    if (n[ip+k] == n[jp+k]) {
      if (k == p) {
        jp += p;
        k = 1;
      } else k++;
    } else if (n[ip+k] < n[jp+k]) {
      jp += k;
      k = 1;
      p = jp - ip;
    } else {
      ip = jp++;
      k = p = 1;
    }
  }
  if (ip+1 > ms+1) ms = ip;
  else p = p0;

  /* Periodic needle? */
  if (memcmp(n, n+p, ms+1)) {
    mem0 = 0;
    p = MAX(ms, l-ms-1) + 1;
  } else mem0 = l-p;
  mem = 0;

  /* Initialize incremental end-of-haystack pointer */
  z = h;

  /* Search loop */
  for (;;) {
    /* Update incremental end-of-haystack pointer */
    if (z-h < l) {
      /* Fast estimate for MIN(l,63) */
      size_t grow = l | 63;
      const unsigned char *z2 = memchr(z, 0, grow);
      if (z2) {
        z = z2;
        if (z-h < l) return 0;
      } else z += grow;
    }

    /* Check last byte first; advance by shift on mismatch */
    if (BITOP(byteset, h[l-1], &)) {
      k = l-shift[h[l-1]];
      if (k) {
        if (k < mem) k = mem;
        h += k;
        mem = 0;
        continue;
      }
    } else {
      h += l;
      mem = 0;
      continue;
    }

    /* Compare right half */
    for (k=MAX(ms+1,mem); n[k] && n[k] == h[k]; k++);
    if (n[k]) {
      h += k-ms;
      mem = 0;
      continue;
    }
    /* Compare left half */
    for (k=ms+1; k>mem && n[k-1] == h[k-1]; k--);
    if (k <= mem) return (char *)h;
    h += p;
    mem = mem0;
  }
}

char *strstr(const char *h, const char *n)
{
  /* Return immediately on empty needle */
  if (!n[0]) return (char *)h;

  /* Use faster algorithms for short needles */
  h = strchr(h, *n);
  if (!h || !n[1]) return (char *)h;
  if (!h[1]) return 0;
  if (!n[2]) return twobyte_strstr((void *)h, (void *)n);
  if (!h[2]) return 0;
  if (!n[3]) return threebyte_strstr((void *)h, (void *)n);
  if (!h[3]) return 0;
  if (!n[4]) return fourbyte_strstr((void *)h, (void *)n);

  return twoway_strstr((void *)h, (void *)n);
}

/***************************************************************************
 * 7.24.6 Miscellaneous functions
 ***************************************************************************/

void* memset(void *s, int c, size_t n)
{
  unsigned char *p = s;
  while (n--)
    *p++ = (unsigned char)c;
  return s;
}

char *strerror(int errnum)
{
  assert(0 && "not supported");
  _Exit(127);
  return NULL;
}

size_t strlen(const char *s)
{
  size_t len = 0;
  while(*s) len++, s++;
  return len;
}


/***************************************************************************
 * POSIX
 ***************************************************************************/

char* strdup(const char *s)
{
  void *malloc(size_t);
  size_t len = strlen(s)+1;
  char *sc = malloc(len);
  memcpy(sc, s, len);
  return sc;
}


/***************************************************************************
 * GNU Extension
 ***************************************************************************/

char *strchrnul(const char *s, int c)
{
  c = (unsigned char)c;
  if (!c) return (char *)s + strlen(s);
  for (; *s && *(unsigned char *)s != c; s++);
  return (char *)s;
}



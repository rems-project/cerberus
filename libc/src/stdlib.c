#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <limits.h>
#include <stdint.h>
#include <signal.h>
#include <assert.h>
#include "stdlib.h"

/***************************************************************************
 * 7.22.1 Numeric conversion functions
 ***************************************************************************/

int atoi(const char *s)
{
  int n=0, neg=0;
  while (isspace(*s)) s++;
  switch (*s) {
  case '-': neg=1;
  case '+': s++;
  }
  /* Compute n as a negative number to avoid overflow on INT_MIN */
  while (isdigit(*s))
    n = 10*n - (*s++ - '0');
  return neg ? n : -n;
}

long atol(const char *s)
{
  long n=0;
  int neg=0;
  while (isspace(*s)) s++;
  switch (*s) {
  case '-': neg=1;
  case '+': s++;
  }
  /* Compute n as a negative number to avoid overflow on LONG_MIN */
  while (isdigit(*s))
    n = 10*n - (*s++ - '0');
  return neg ? n : -n;
}

long long atoll(const char *s)
{
  long long n=0;
  int neg=0;
  while (isspace(*s)) s++;
  switch (*s) {
  case '-': neg=1;
  case '+': s++;
  }
  /* Compute n as a negative number to avoid overflow on LLONG_MIN */
  while (isdigit(*s))
    n = 10*n - (*s++ - '0');
  return neg ? n : -n;
}

double atof(const char *s)
{
  return strtod(s, 0);
}

// stdio.c
long double __strtoxd(const char *s, char **p, int prec);

float strtof(const char *restrict s, char **restrict p)
{
  return __strtoxd(s, p, 0);
}

double strtod(const char *restrict s, char **restrict p)
{
  return __strtoxd(s, p, 1);
}

long double strtold(const char *restrict s, char **restrict p)
{
  return __strtoxd(s, p, 2);
}

// stdio.c
unsigned long long __strtox(const char *, char **, int, unsigned long long);

unsigned long long strtoull(const char *restrict s, char **restrict p, int base)
{
  return __strtox(s, p, base, ULLONG_MAX);
}

long long strtoll(const char *restrict s, char **restrict p, int base)
{
  return __strtox(s, p, base, LLONG_MIN);
}

unsigned long strtoul(const char *restrict s, char **restrict p, int base)
{
  return __strtox(s, p, base, ULONG_MAX);
}

long strtol(const char *restrict s, char **restrict p, int base)
{
  return __strtox(s, p, base, 0UL+LONG_MIN);
}

/***************************************************************************
 * 7.22.2 Pseudo-random sequence generation functions
 ***************************************************************************/

static unsigned long int __seed = 1;
int rand(void)
{
  __seed = __seed * 1103515245 + 12345;
  return (unsigned int)(__seed/65536) % RAND_MAX;
}

void srand(unsigned int seed)
{
  __seed = seed;
}


/***************************************************************************
 * 7.22.3 Memory management functions
 ***************************************************************************/

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

/***************************************************************************
 * 7.22.4 Communication with the environment
 ***************************************************************************/

_Noreturn void abort(void)
{
  raise(SIGABRT);
  _Exit(127);
}

/* Ensure that at least 32 atexit handlers can be registered without malloc */
#define COUNT 32

static struct fl
{
  struct fl *next;
  void (*f[COUNT])(void *);
  void *a[COUNT];
} builtin, *head;

static int slot;

static void __funcs_on_exit()
{
  void (*func)(void *), *arg;
  for (; head; head=head->next, slot=COUNT) while(slot-->0) {
    func = head->f[slot];
    arg = head->a[slot];
    func(arg);
  }
}

int __cxa_atexit(void (*func)(void *), void *arg, void *dso)
{
  /* Defer initialization of head so it can be in BSS */
  if (!head) head = &builtin;

  /* If the current function list is full, add a new one */
  if (slot==COUNT) {
    struct fl *new_fl = calloc(sizeof(struct fl), 1);
    if (!new_fl) {
      return -1;
    }
    new_fl->next = head;
    head = new_fl;
    slot = 0;
  }

  /* Append function to the list. */
  head->f[slot] = func;
  head->a[slot] = arg;
  slot++;

  return 0;
}

static void call(void *p)
{
  ((void (*)(void))(uintptr_t)p)();
}

int atexit(void (*func)(void))
{
  return __cxa_atexit(call, (void *)(uintptr_t)func, 0);
}

static void (*funcs[COUNT])(void);
static int count;

static void __funcs_on_quick_exit()
{
  void (*func)(void);
  while (count > 0) {
    func = funcs[--count];
    func();
  }
}

int at_quick_exit(void (*func)(void))
{
  int r = 0;
  if (count == 32) r = -1;
  else funcs[count++] = func;
  return r;
}


_Noreturn void exit(int code)
{
  __funcs_on_exit();
  _Exit(code);
}

_Noreturn void quick_exit(int code)
{
  __funcs_on_quick_exit();
  _Exit(code);
}

_Noreturn void _Exit(int ec)
{
  _Noreturn void __builtin_exit(int);
  __builtin_exit(ec);
}

// TODO: not sure about this!!
// I might need to include as a Cerberus variable
static char **__environ;

static char *__strchrnul(const char *s, int c)
{
  c = (unsigned char)c;
  if (!c) return (char *)s + strlen(s);
  for (; *s && *(unsigned char *)s != c; s++);
  return (char *)s;
}

char *getenv(const char *name)
{
  size_t l = __strchrnul(name, '=') - (char*)name;
  if (l && !name[l] && __environ)
    for (char **e = __environ; *e; e++)
      if (!strncmp(name, *e, l) && l[*e] == '=')
        return *e + l+1;
  return 0;
}

int system(const char *string)
{
  // Command processor is not available in Cerberus.
  return 0;
}

/***************************************************************************
 * 7.22.5 Searching and sorting utilities
 ***************************************************************************/

void *bsearch(const void *key, const void *base, size_t nel, size_t width, int (*cmp)(const void *, const void *))
{
  void *try;
  int sign;
  while (nel > 0) {
    try = (char *)base + width*(nel/2);
    sign = cmp(key, try);
    if (sign < 0) {
      nel /= 2;
    } else if (sign > 0) {
      base = (char *)try + width;
      nel -= nel/2+1;
    } else {
      return try;
    }
  }
  return NULL;
}

typedef int (*cmpfun)(const void *, const void *);

static inline int pntz(size_t p[2]) {
  int r = (p[0] - 1);
  if(r != 0 || (r = 8*sizeof(size_t) + (p[1])) != 8*sizeof(size_t)) {
    return r;
  }
  return 0;
}

static void cycle(size_t width, unsigned char* ar[], int n)
{
  unsigned char tmp[256];
  size_t l;
  int i;

  if(n < 2) {
    return;
  }

  ar[n] = tmp;
  while(width) {
    l = sizeof(tmp) < width ? sizeof(tmp) : width;
    memcpy(ar[n], ar[0], l);
    for(i = 0; i < n; i++) {
      memcpy(ar[i], ar[i + 1], l);
      ar[i] += l;
    }
    width -= l;
  }
}

/* shl() and shr() need n > 0 */
static inline void shl(size_t p[2], int n)
{
  if(n >= 8 * sizeof(size_t)) {
    n -= 8 * sizeof(size_t);
    p[1] = p[0];
    p[0] = 0;
  }
  p[1] <<= n;
  p[1] |= p[0] >> (sizeof(size_t) * 8 - n);
  p[0] <<= n;
}

static inline void shr(size_t p[2], int n)
{
  if(n >= 8 * sizeof(size_t)) {
    n -= 8 * sizeof(size_t);
    p[0] = p[1];
    p[1] = 0;
  }
  p[0] >>= n;
  p[0] |= p[1] << (sizeof(size_t) * 8 - n);
  p[1] >>= n;
}

static void sift(unsigned char *head, size_t width, cmpfun cmp, int pshift, size_t lp[])
{
  unsigned char *rt, *lf;
  unsigned char *ar[14 * sizeof(size_t) + 1];
  int i = 1;

  ar[0] = head;
  while(pshift > 1) {
    rt = head - width;
    lf = head - width - lp[pshift - 2];

    if((*cmp)(ar[0], lf) >= 0 && (*cmp)(ar[0], rt) >= 0) {
      break;
    }
    if((*cmp)(lf, rt) >= 0) {
      ar[i++] = lf;
      head = lf;
      pshift -= 1;
    } else {
      ar[i++] = rt;
      head = rt;
      pshift -= 2;
    }
  }
  cycle(width, ar, i);
}

static void trinkle(unsigned char *head, size_t width, cmpfun cmp, size_t pp[2], int pshift, int trusty, size_t lp[])
{
  unsigned char *stepson,
                *rt, *lf;
  size_t p[2];
  unsigned char *ar[14 * sizeof(size_t) + 1];
  int i = 1;
  int trail;

  p[0] = pp[0];
  p[1] = pp[1];

  ar[0] = head;
  while(p[0] != 1 || p[1] != 0) {
    stepson = head - lp[pshift];
    if((*cmp)(stepson, ar[0]) <= 0) {
      break;
    }
    if(!trusty && pshift > 1) {
      rt = head - width;
      lf = head - width - lp[pshift - 2];
      if((*cmp)(rt, stepson) >= 0 || (*cmp)(lf, stepson) >= 0) {
        break;
      }
    }

    ar[i++] = stepson;
    head = stepson;
    trail = pntz(p);
    shr(p, trail);
    pshift += trail;
    trusty = 0;
  }
  if(!trusty) {
    cycle(width, ar, i);
    sift(head, width, cmp, pshift, lp);
  }
}

void qsort(void *base, size_t nel, size_t width, cmpfun cmp)
{
  size_t lp[12*sizeof(size_t)];
  size_t i, size = width * nel;
  unsigned char *head, *high;
  size_t p[2] = {1, 0};
  int pshift = 1;
  int trail;

  if (!size) return;

  head = base;
  high = head + size - width;

  /* Precompute Leonardo numbers, scaled by element width */
  for(lp[0]=lp[1]=width, i=2; (lp[i]=lp[i-2]+lp[i-1]+width) < size; i++);

  while(head < high) {
    if((p[0] & 3) == 3) {
      sift(head, width, cmp, pshift, lp);
      shr(p, 2);
      pshift += 2;
    } else {
      if(lp[pshift - 1] >= high - head) {
        trinkle(head, width, cmp, p, pshift, 0, lp);
      } else {
        sift(head, width, cmp, pshift, lp);
      }
      
      if(pshift == 1) {
        shl(p, 1);
        pshift = 0;
      } else {
        shl(p, pshift - 1);
        pshift = 1;
      }
    }
    
    p[0] |= 1;
    head += width;
  }

  trinkle(head, width, cmp, p, pshift, 0, lp);

  while(pshift != 1 || p[0] != 1 || p[1] != 0) {
    if(pshift <= 1) {
      trail = pntz(p);
      shr(p, trail);
      pshift += trail;
    } else {
      shl(p, 2);
      pshift -= 2;
      p[0] ^= 7;
      shr(p, 1);
      trinkle(head - lp[pshift] - width, width, cmp, p, pshift + 1, 1, lp);
      shl(p, 1);
      p[0] |= 1;
      trinkle(head - width, width, cmp, p, pshift, 1, lp);
    }
    head -= width;
  }
}

/***************************************************************************
 * 7.22.6 Integer arithmetic functions
 ***************************************************************************/

int abs(int a)
{
  return a>0 ? a : -a;
}

long labs(long a)
{
  return a>0 ? a : -a;
}

long long llabs(long long a)
{
  return a>0 ? a : -a;
}

div_t div(int num, int den)
{
  return (div_t){ num/den, num%den };
}

ldiv_t ldiv(long num, long den)
{
  return (ldiv_t){ num/den, num%den };
}

lldiv_t lldiv(long long num, long long den)
{
  return (lldiv_t){ num/den, num%den };
}

/***************************************************************************
 * 7.22.7 Multibyte/wide character conversion functions
 ***************************************************************************/

int mblen(const char *s, size_t n)
{
  assert(0 && "not supported");
  _Exit(127);
}

int mbtowc(wchar_t * restrict pwc, const char * restrict s, size_t n)
{
  assert(0 && "not supported");
  _Exit(127);
}

int wctomb(char *s, wchar_t wchar)
{
  assert(0 && "not supported");
  _Exit(127);
}

/***************************************************************************
 * 7.22.8 Multibyte/wide string conversion functions
 ***************************************************************************/

size_t mbstowcs(wchar_t * restrict pwcs, const char * restrict s, size_t n)
{
  assert(0 && "not supported");
  _Exit(127);
}

size_t wcstombs(char * restrict s, const wchar_t * restrict pwcs, size_t n)
{
  assert(0 && "not supported");
  _Exit(127);
}


#ifndef	_STDLIB_H_
#define	_STDLIB_H_

typedef __cerbty_size_t size_t;
typedef __cerbty_wchar_t wchar_t;

typedef struct div { int quot, rem; } div_t;
typedef struct ldiv { long quot, rem; } ldiv_t;
typedef struct lldiv { long long quot, rem; } lldiv_t;

#define NULL __cerbvar_NULL

#define EXIT_FAILURE 1
#define EXIT_SUCCESS 0

#define MB_CUR_MAX   __cerbvar_MB_CUR_MAX
#define RAND_MAX    (0x7fffffff)

int atoi (const char *);
long atol (const char *);
long long atoll (const char *);
double atof (const char *);

double strtod(const char * restrict nptr, char ** restrict endptr);
float strtof(const char * restrict nptr, char ** restrict endptr);
long double strtold(const char * restrict nptr, char ** restrict endptr);

long int strtol(const char * restrict, char ** restrict, int);
long long int strtoll(const char * restrict, char ** restrict, int);
unsigned long int strtoul(const char * restrict, char ** restrict, int);
unsigned long long int strtoull(const char * restrict, char ** restrict, int);

int rand(void);
void srand(unsigned int seed);

void *aligned_alloc(size_t alignment, size_t size);
void *calloc(size_t nmemb, size_t size);
void free(void *ptr);
void *malloc(size_t size);
void *realloc(void *ptr, size_t size);

_Noreturn void abort(void);
int atexit(void (*func)(void));
int at_quick_exit(void (*func)(void));
_Noreturn void exit(int status);
_Noreturn void _Exit(int status);
_Noreturn void quick_exit(int status);

char *getenv(const char *name);
int system(const char *string);

void *bsearch(const void *key, const void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *));
void qsort(void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *));

int abs(int j);
long int labs(long int j);
long long int llabs(long long int j);

div_t div(int numer, int denom);
ldiv_t ldiv(long int numer, long int denom);
lldiv_t lldiv(long long int numer, long long int denom);

int mblen(const char *s, size_t n);
int mbtowc(wchar_t * restrict pwc, const char * restrict s, size_t n);
int wctomb(char *s, wchar_t wchar);

size_t mbstowcs(wchar_t * restrict pwcs, const char * restrict s, size_t n);
size_t wcstombs(char * restrict s, const wchar_t * restrict pwcs, size_t n);

#endif

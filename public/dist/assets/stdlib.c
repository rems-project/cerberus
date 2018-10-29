/**
 * Available library functions
 *
 **/

// <ctype.h>
int isblank(int c);
int iscntrl(int c);
int isdigit(int c);
int isgraph(int c);
int isprint(int c);
int isspace(int c);
int islower(int c);
int isupper(int c);
int isalpha(int c);
int isalnum(int c);
int ispunct(int c);
int isxdigit(int c);
int tolower(int c);
int toupper(int c);

// <stdio.h>
int printf(const char * restrict format, ...);
int sprintf(char * restrict s, const char * restrict format, ...);
int snprintf(char * restrict s, size_t n, const char * restrict format, ...);
int putchar(int c);
int puts(const char *s);

// <stdlib.h>
void *malloc(size_t size);
void *calloc(size_t nmemb, size_t size);
void *realloc(void *ptr, size_t size);
void free(void *ptr);
int abs(int i);
int atoi(const char *nptr);
int rand(void);
void srand(unsigned int seed);
_Noreturn void exit(int status);
_Noreturn void _Exit(int status);
_Noreturn void abort(void);

// <string.h>
void *memcpy(void * restrict s1, const void * restrict s2, size_t n);
int memcmp(const void *s1, const void *s2, size_t n);
char *strcpy (char * restrict s1, const char * restrict s2);
char *strncpy (char * restrict s1, const char * restrict s2, size_t n);
void* memset(void *s, int c, size_t n);
int strcmp (const char *s1, const char *s2);
int strncmp(const char *s1, const char *s2, size_t n);
size_t strlen(const char *s);
char *strcat(char * restrict s1, const char * restrict s2);
char *strchr(const char *s, int n);
char *strrchr(const char *s, int n);
char* strdup(const char *s);



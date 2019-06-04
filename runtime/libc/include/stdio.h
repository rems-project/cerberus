#ifndef _STDIO_H_
#define _STDIO_H_

#include <stdarg.h>

typedef __cerbty_size_t size_t;

typedef struct _IO_FILE FILE;

typedef union _G_fpos64_t {
  char __opaque[16];
  long long __lldata;
  double __align;
} fpos_t;

#define NULL          __cerbvar_NULL

#define BUFSIZ        1024
#define EOF           -1
#define FOPEN_MAX     1000
#define FILENAME_MAX  4096

#define L_tmpnam      20

#define SEEK_SET      0
#define SEEK_CUR      1
#define SEEK_END      2

#define TMP_MAX       10000

extern FILE *const __stdout;
extern FILE *const __stderr;
extern FILE *const __stdin;

#define stdout  __stdout
#define stderr  __stderr
#define stdin   __stdin

#define _IOFBF 0
#define _IOLBF 1
#define _IONBF 2

int remove(const char *filename);
int rename(const char *old, const char *new);
FILE *tmpfile(void);
char *tmpnam(char *s);

int fclose(FILE *stream);
int fflush(FILE *stream);
FILE *fopen(const char * restrict filename, const char * restrict mode);
FILE *freopen(const char * restrict filename, const char * restrict mode, FILE * restrict stream);

void setbuf(FILE * restrict stream, char * restrict buf);
int setvbuf(FILE * restrict stream, char * restrict buf, int mode, size_t size);

int fprintf(FILE * restrict stream, const char * restrict fmt, ...);
int fscanf(FILE * restrict stream, const char * restrict fmt, ...);

int printf(const char * restrict fmt, ...);
int scanf(const char * restrict fmt, ...);

#if __bmc_cerb__
#define printf(...)
#endif

int snprintf(char * restrict s, size_t n, const char * restrict fmt, ...);
int sprintf(char * restrict s, const char * restrict fmt, ...);
int sscanf(const char * restrict s, const char * restrict fmt, ...);

int vfprintf(FILE * restrict stream, const char * restrict fmt, va_list arg);
int vfscanf(FILE * restrict stream, const char * restrict fmt, va_list arg);

int vprintf(const char * restrict fmt, va_list arg);
int vscanf(const char * restrict fmt, va_list arg);

int vsnprintf(char * restrict s, size_t n, const char * restrict fmt, va_list arg);
int vsprintf(char * restrict s, const char * restrict fmt, va_list arg);
int vsscanf(const char * restrict s, const char * restrict fmt, va_list arg);

int fgetc(FILE *stream);
char *fgets(char * restrict s, int n, FILE * restrict stream);

int fputc(int c, FILE *stream);
int fputs(const char * restrict s, FILE * restrict stream);

int getc(FILE *stream);
int getchar(void);

int putc(int c, FILE *stream);
int putchar(int c);

int puts(const char *s);
int ungetc(int c, FILE *stream);

size_t fread(void * restrict p, size_t size, size_t nmemb, FILE * restrict stream);
size_t fwrite(const void * restrict p, size_t size, size_t nmemb, FILE * restrict stream);

int fgetpos(FILE * restrict stream, fpos_t * restrict pos);
int fseek(FILE *stream, long int offset, int whence);
int fsetpos(FILE *stream, const fpos_t *pos);
long int ftell(FILE *stream);
void rewind(FILE *stream);
void clearerr(FILE *stream);
int feof(FILE *stream);
int ferror(FILE *stream);
void perror(const char *s);

#include "posix/stdio.h"

#endif

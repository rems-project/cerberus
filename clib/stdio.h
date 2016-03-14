#ifndef	_STDIO_H_
#define	_STDIO_H_

#include <stdarg.h>

#if !defined(_STDLIB_H_) && !defined(_STRING_H_) // TODO: fix the f!cking parser
typedef __cerbty_size_t size_t;
#endif
typedef __cerbty_FILE   FILE;
typedef __cerbty_fpos_t fpos_t;

#define NULL         __cerbvar_NULL
#define IOFBF        __cerbvar_IOFBF
#define IOLBF        __cerbvar_IOLBF
#define IONBF        __cerbvar_IONBF
#define BUFSIZ       __cerbvar_BUFSIZ
#define EOF          __cerbvar_EOF
#define FOPEN_MAX    __cerbvar_FOPEN_MAX
#define FILENAME_MAX __cerbvar_FILENAME_MAX
#define L_tmpnam     __cerbvar_L_tmpnam
#define SEEK_CUR     __cerbvar_SEEK_CUR
#define SEEK_END     __cerbvar_SEEK_END
#define SEEK_SET     __cerbvar_SEEK_SET
#define TMP_MAX      __cerbvar_TMP_MAX
#define stderr       __cerbvar_stderr
#define stdin        __cerbvar_stdin
#define stdout       __cerbvar_stdout


// TEMPORARY HACK
#define restrict

int remove(const char *filename); // FILE
int rename(const char *old, const char *new); // FILE
FILE *tmpfile(void); // FILE
char *tmpnam(char *s); // FILE
int fclose(FILE *stream); // FILE
int fflush(FILE *stream); // FILE
FILE *fopen(const char * restrict filename, const char * restrict mode); // FILE
FILE *freopen(const char * restrict filename, const char * restrict mode, FILE * restrict stream); // FILE
void setbuf(FILE * restrict stream, char * restrict buf); // FILE
int setvbuf(FILE * restrict stream, char * restrict buf, int mode, size_t size); // FILE
int fprintf(FILE * restrict stream, const char * restrict format, ...); // FILE
int fscanf(FILE * restrict stream, const char * restrict format, ...); // FILE

int printf(const char * restrict format, ...);
int scanf(const char * restrict format, ...);
int snprintf(char * restrict s, size_t n, const char * restrict format, ...);
int sprintf(char * restrict s, const char * restrict format, ...);
int sscanf(const char * restrict s, const char * restrict format, ...);
int vfprintf(FILE * restrict stream, const char * restrict format, va_list arg); // FILE
int vfscanf(FILE * restrict stream, const char * restrict format, va_list arg); // FILE
int vprintf(const char * restrict format, va_list arg);
int vscanf(const char * restrict format, va_list arg);
int vsnprintf(char * restrict s, size_t n, const char * restrict format, va_list arg);
int vsprintf(char * restrict s, const char * restrict format, va_list arg);
int vsscanf(const char * restrict s, const char * restrict format, va_list arg);
int fgetc(FILE *stream); // FILE
char *fgets(char * restrict s, int n, FILE * restrict stream); // FILE
int fputc(int c, FILE *stream); // FILE
int fputs(const char * restrict s, FILE * restrict stream); // FILE
int getc(FILE *stream); // FILE
int getchar(void);
int putc(int c, FILE *stream); // FILE
int putchar(int c);
int puts(const char *s);
int ungetc(int c, FILE *stream); // FILE
size_t fread(void * restrict ptr, size_t size, size_t nmemb, FILE * restrict stream); // FILE
size_t fwrite(const void * restrict ptr, size_t size, size_t nmemb, FILE * restrict stream); // FILE
int fgetpos(FILE * restrict stream, fpos_t * restrict pos); // FILE
int fseek(FILE *stream, long int offset, int whence); // FILE
int fsetpos(FILE *stream, const fpos_t *pos); // FILE
long int ftell(FILE *stream); // FILE
void rewind(FILE *stream); // FILE
void clearerr(FILE *stream); // FILE
int feof(FILE *stream); // FILE
int ferror(FILE *stream); // FILE
void perror(const char *s);

// Annex K: Bounds-checking interfaces
//TODO: L_tmpnam_s TMP_MAX_S
typedef int errno_t;
typedef size_t rsize_t;


errno_t tmpfile_s(FILE * restrict * restrict streamptr);
errno_t tmpnam_s(char *s, rsize_t maxsize);

errno_t fopen_s(FILE * restrict * restrict streamptr, const char * restrict filename, const char * restrict mode); // FILE
errno_t freopen_s(FILE * restrict * restrict newstreamptr, const char * restrict filename, const char * restrict mode, FILE * restrict stream);  // FILE
int fprintf_s(FILE * restrict stream, const char * restrict format, ...); // FILE
int fscanf_s(FILE * restrict stream, const char * restrict format, ...); // FILE
int printf_s(const char * restrict format, ...);
int scanf_s(const char * restrict format, ...);
int snprintf_s(char * restrict s, rsize_t n, const char * restrict format, ...);
int sprintf_s(char * restrict s, rsize_t n, const char * restrict format, ...);
int sscanf_s(const char * restrict s, const char * restrict format, ...);
int vfprintf_s(FILE * restrict stream, const char * restrict format, va_list arg); // FILE
int vfscanf_s(FILE * restrict stream, const char * restrict format, va_list arg); // FILE
int vprintf_s(const char * restrict format, va_list arg);
int vscanf_s(const char * restrict format, va_list arg);
int vsnprintf_s(char * restrict s, rsize_t n, const char * restrict format, va_list arg);
int vsprintf_s(char * restrict s, rsize_t n, const char * restrict format, va_list arg);
int vsscanf_s(const char * restrict s, const char * restrict format, va_list arg);
char *gets_s(char *s, rsize_t n);




#else
#endif

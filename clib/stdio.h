// TODO: Things having to do with files are left for later.


/* (§7.21.1) Introduction */
typedef __cerb_size_t size_t;
// FILE
// fpos_t
#define NULL __cerb_NULL
// _IOLBF
// _IONBF
// _IOFBF
// BUFSIZ
// EOF
// FOPEN_MAX
// FILENAME_MAX
// L_tmpnam
// SEEK_CUR
// SEEK_END
// SEEK_SET
// TMP_MAX
// stderr
// stdin
// stdout


/* (§7.21.4) Operations on files */

// int remove(const char *filename);
// int rename(const char *old, const char *new);
// FILE *tmpfile(void);
// char *tmpnam(char *s);


/* (§7.21.5) File access functions */

// int fclose(FILE *stream);
// int fflush(FILE *stream);
// FILE *fopen(const char * restrict filename, const char * restrict mode);
// FILE *freopen(const char * restrict filename, const char * restrict mode, FILE * restrict stream);
// void setbuf(FILE * restrict stream, char * restrict buf);
// int setvbuf(FILE * restrict stream, char * restrict buf, int mode, size_t size);


/* (§7.21.6) Formatted input/output functions */

// int fprintf(FILE * restrict stream, const char * restrict format, ...);
// int fscanf(FILE * restrict stream, const char * restrict format, ...);
int printf(const char * restrict format, ...);
int scanf(const char * restrict format, ...);
int snprintf(char * restrict s, size_t n, const char * restrict format, ...);
int sprintf(char * restrict s, const char * restrict format, ...);
int sscanf(const char * restrict s, const char * restrict format, ...);
// int vfprintf(FILE * restrict stream, const char * restrict format, va_list arg);
// int vfscanf(FILE * restrict stream, const char * restrict format, va_list arg);
// TODO[VA_LIST]  int vprintf(const char * restrict format, va_list arg);
// TODO[VA_LIST]  int vscanf(const char * restrict format, va_list arg);
// TODO[VA_LIST]  int vsnprintf(char * restrict s, size_t n, const char * restrict format, va_list arg);
// TODO[VA_LIST]  int vsprintf(char * restrict s, const char * restrict format, va_list arg);
// TODO[VA_LIST]  int vsscanf(const char * restrict s, const char * restrict format, va_list arg);


/* (§7.21.7) Character input/output functions */

// int fgetc(FILE *stream);
// char *fgets(char * restrict s, int n, FILE * restrict stream);
// int fputc(int c, FILE *stream);
// int fputs(const char * restrict s, FILE * restrict stream);
// int getc(FILE *stream);
int getchar(void);
// int putc(int c, FILE *stream);
int putchar(int c);
int puts(const char *s);
// int ungetc(int c, FILE *stream);


/* (§7.21.8) Direct input/output functions */

// size_t fread(void * restrict ptr, size_t size, size_t nmemb, FILE * restrict stream);
// size_t fwrite(const void * restrict ptr, size_t size, size_t nmemb, FILE * restrict stream);


/* (§7.21.9) File positioning functions */

// int fgetpos(FILE * restrict stream, fpos_t * restrict pos);
// int fseek(FILE *stream, long int offset, int whence);
// int fsetpos(FILE *stream, const fpos_t *pos);
// long int ftell(FILE *stream);
// void rewind(FILE *stream);


/* (§7.21.10) Error-handling functions */
// void clearerr(FILE *stream);
// int feof(FILE *stream);
// int ferror(FILE *stream);
void perror(const char *s);



/* TODO */
// __STDC_WANT_LIB_EXT1__
// L_tmpnam_s
// TMP_MAX_S
// errno_t
// rsize_t

// errno_t tmpfile_s(FILE * restrict * restrict streamptr);
// errno_t tmpnam_s(char *s, rsize_t maxsize);
// errno_t fopen_s(FILE * restrict * restrict streamptr, const char * restrict filename, const char * restrict mode);
// errno_t freopen_s(FILE * restrict * restrict newstreamptr, const char * restrict filename, const char * restrict mode, FILE * restrict stream);
// int fprintf_s(FILE * restrict stream, const char * restrict format, ...);
// int fscanf_s(FILE * restrict stream, const char * restrict format, ...);
// int printf_s(const char * restrict format, ...);
// int scanf_s(const char * restrict format, ...);
// int snprintf_s(char * restrict s, rsize_t n, const char * restrict format, ...);
// int sprintf_s(char * restrict s, rsize_t n, const char * restrict format, ...);
// int sscanf_s(const char * restrict s, const char * restrict format, ...);
// int vfprintf_s(FILE * restrict stream, const char * restrict format, va_list arg);
// int vfscanf_s(FILE * restrict stream, const char * restrict format, va_list arg);
// int vprintf_s(const char * restrict format, va_list arg);
// int vscanf_s(const char * restrict format, va_list arg);
// int vsnprintf_s(char * restrict s, rsize_t n, const char * restrict format, va_list arg);
// int vsprintf_s(char * restrict s, rsize_t n, const char * restrict format, va_list arg);
// int vsscanf_s(const char * restrict s, const char * restrict format, va_list arg);
// char *gets_s(char *s, rsize_t n);

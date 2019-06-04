#ifndef _INTERNAL_H_
#define _INTERNAL_H_

#include <stdio.h>
#include <sys/types.h>

struct _IO_FILE {
  unsigned flags;
  unsigned char *rpos, *rend;
  int (*close)(FILE *);
  unsigned char *wend, *wpos;
  unsigned char *mustbezero_1;
  unsigned char *wbase;
  size_t (*read)(FILE *, unsigned char *, size_t);
  size_t (*write)(FILE *, const unsigned char *, size_t);
  off_t (*seek)(FILE *, off_t, int);
  unsigned char *buf;
  size_t buf_size;
  FILE *prev, *next;
  int fd;
  int pipe_pid;
  long lockcount;
  int mode;
  volatile int lock;
  int lbf;
  void *cookie;
  off_t off;
  char *getln_buf;
  void *mustbezero_2;
  unsigned char *shend;
  off_t shlim, shcnt;
  FILE *prev_locked, *next_locked;
  struct __locale_struct *locale;
};

static int __stdio_close(FILE *f);
static off_t __stdio_seek(FILE *f, off_t off, int whence);
static size_t __stdio_read(FILE *f, unsigned char *buf, size_t len);
static size_t __stdio_write(FILE *f, const unsigned char *buf, size_t len);
static size_t __stdout_write(FILE *f, const unsigned char *buf, size_t len);

#define shcnt(f) ((f)->shcnt + ((f)->rpos - (f)->buf))
#define fshlim(f, lim) __shlim((f), (lim))
#define shgetc(f) (((f)->rpos != (f)->shend) ? *(f)->rpos++ : __shgetc(f))
#define shunget(f) ((f)->shend != NULL ? (void)(f)->rpos-- : (void)0)

int __shgetc(FILE *f);
void __shlim(FILE *f, off_t lim);


long double __floatscan(FILE *f, int prec, int pok);
unsigned long long __intscan(FILE *f, unsigned base, int pok, unsigned long long lim);

#endif



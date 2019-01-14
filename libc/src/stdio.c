#include "errno.h"
#include "string.h"
#include "stdlib.h"
#include "time.h"
#include "stdarg.h"

#include "unistd.h"
#include "fcntl.h"
#include "sys/uio.h"
#include "sys/stat.h"
#include "sys/types.h"

#include "internal.h"
#include "stdio.h"

#define MAYBE_WAITERS 0x40000000

#define MIN(a,b) ((a)<(b) ? (a) : (b))

#define MAXTRIES 100
#define UNGET 8

#undef getc_unlocked
#define getc_unlocked(f) \
  ( ((f)->rpos != (f)->rend) ? *(f)->rpos++ : __uflow((f)) )

#define putc_unlocked(c, f) \
  ( (((unsigned char)(c)!=(f)->lbf && (f)->wpos!=(f)->wend)) \
  ? *(f)->wpos++ = (unsigned char)(c) \
  : __overflow((f),(unsigned char)(c)) )

#define sh_fromstring(f, s) \
  ((f)->buf = (f)->rpos = (void *)(s), (f)->rend = (void*)-1)

#define F_PERM 1
#define F_NORD 4
#define F_NOWR 8
#define F_EOF 16
#define F_ERR 32
#define F_SVB 64
#define F_APP 128

/***************************************************************************
 * Globals
 ***************************************************************************/

static FILE *ofl_head;

static unsigned char __stdout_buf[BUFSIZ+UNGET];
static FILE __stdout_FILE = {
  .flags = F_PERM | F_NORD,
  .close = __stdio_close,
  .write = __stdout_write,
  .seek = __stdio_seek,
  .buf = __stdout_buf+UNGET,
  .buf_size = sizeof __stdout_buf-UNGET,
  .fd = 1,
  .lock = -1,
  .lbf = '\n',
};
FILE *const __stdout = &__stdout_FILE;
FILE *volatile __stdout_used = &__stdout_FILE;

static unsigned char __stdin_buf[BUFSIZ+UNGET];
static FILE __stdin_FILE = {
  .flags = F_PERM | F_NOWR,
  .close = __stdio_close,
  .read = __stdio_read,
  .seek = __stdio_seek,
  .buf = __stdin_buf+UNGET,
  .buf_size = sizeof __stdin_buf-UNGET,
  .fd = 0,
  .lock = -1,
};
FILE *const __stdin = &__stdin_FILE;
FILE *volatile __stdin_used = &__stdin_FILE;

static unsigned char __stderr_buf[UNGET];
static FILE __stderr_FILE = {
  .flags = F_PERM | F_NORD,
  .close = __stdio_close,
  .write = __stdio_write,
  .seek = __stdio_seek,
  .buf = __stderr_buf+UNGET,
  .buf_size = 0,
  .fd = 2,
  .lock = -1,
  .lbf = -1,
};
FILE *const __stderr = &__stderr_FILE;
FILE *volatile __stderr_used = &__stderr_FILE;

/***************************************************************************
 * Internal functions
 ***************************************************************************/

/* This assumes that a check for the
   template size has already been made */
static char *__randname(char *template)
{
  int i;
  struct timespec ts;
  unsigned long r;

  clock_gettime(CLOCK_REALTIME, &ts);
  r = ts.tv_nsec*65537 ^ (uintptr_t)&ts / 16 + (uintptr_t)template;
  for (i=0; i<6; i++, r>>=5)
    template[i] = 'A'+(r&15)+(r&16)*2;

  return template;
}

void __shlim(FILE *f, off_t lim)
{
  f->shlim = lim;
  f->shcnt = f->buf - f->rpos;
  /* If lim is nonzero, rend must be a valid pointer. */
  if (lim && f->rend - f->rpos > lim)
    f->shend = f->rpos + lim;
  else
    f->shend = f->rend;
}

static int __uflow(FILE *f);

int __shgetc(FILE *f)
{
  int c;
  off_t cnt = shcnt(f);
  if ((f->shlim && cnt >= f->shlim) || (c=__uflow(f)) < 0) {
    f->shcnt = f->buf - f->rpos + cnt;
    f->shend = 0;
    return EOF;
  }
  cnt++;
  if (f->shlim && f->rend - f->rpos > f->shlim - cnt)
    f->shend = f->rpos + (f->shlim - cnt);
  else
    f->shend = f->rend;
  f->shcnt = f->buf - f->rpos + cnt;
  if (f->rpos[-1] != c) f->rpos[-1] = c;
  return c;
}

long double __strtoxd(const char *s, char **p, int prec)
{
  FILE f;
  sh_fromstring(&f, s);
  fshlim(&f, 0);
  long double y = __floatscan(&f, prec, 1);
  off_t cnt = shcnt(&f);
  if (p) *p = cnt ? (char *)s + cnt : (char *)s;
  return y;
}


unsigned long long __strtox(const char *s, char **p, int base, unsigned long long lim)
{
  FILE f;
  sh_fromstring(&f, s);
  fshlim(&f, 0);
  unsigned long long y = __intscan(&f, base, 1, lim);
  if (p) {
    size_t cnt = shcnt(&f);
    *p = (char *)s + cnt;
  }
  return y;
}

static int __fmodeflags(const char *mode)
{
  int flags;
  if (strchr(mode, '+')) flags = O_RDWR;
  else if (*mode == 'r') flags = O_RDONLY;
  else flags = O_WRONLY;
  if (strchr(mode, 'x')) flags |= O_EXCL;
  if (strchr(mode, 'e')) flags |= O_CLOEXEC;
  if (*mode != 'r') flags |= O_CREAT;
  if (*mode == 'w') flags |= O_TRUNC;
  if (*mode == 'a') flags |= O_APPEND;
  return flags;
}

static size_t __stdio_read(FILE *f, unsigned char *buf, size_t len)
{
  struct iovec iov[2] = {
    { buf, len - !!f->buf_size },
    { f->buf, f->buf_size }
  };
  ssize_t cnt;

  cnt = iov[0].iov_len ? readv(f->fd, iov, 2)
    : read(f->fd, iov[1].iov_base, iov[1].iov_len);
  if (cnt <= 0) {
    f->flags |= cnt ? F_ERR : F_EOF;
    return 0;
  }
  if (cnt <= iov[0].iov_len) return cnt;
  cnt -= iov[0].iov_len;
  f->rpos = f->buf;
  f->rend = f->buf + cnt;
  if (f->buf_size) buf[len-1] = *f->rpos++;
  return len;
}

static size_t __stdio_write(FILE *f, const unsigned char *buf, size_t len)
{
  struct iovec iovs[2] = {
    { f->wbase, f->wpos-f->wbase },
    { (void *)buf, len }
  };
  struct iovec *iov = iovs;
  size_t rem = iov[0].iov_len + iov[1].iov_len;
  int iovcnt = 2;
  ssize_t cnt;
  for (;;) {
    cnt = writev(f->fd, iov, iovcnt);
    if (cnt == rem) {
      f->wend = f->buf + f->buf_size;
      f->wpos = f->wbase = f->buf;
      return len;
    }
    if (cnt < 0) {
      f->wpos = f->wbase = f->wend = 0;
      f->flags |= F_ERR;
      return iovcnt == 2 ? 0 : len-iov[0].iov_len;
    }
    rem -= cnt;
    if (cnt > iov[0].iov_len) {
      cnt -= iov[0].iov_len;
      iov++; iovcnt--;
    }
    iov[0].iov_base = (char *)iov[0].iov_base + cnt;
    iov[0].iov_len -= cnt;
  }
}

static size_t __stdout_write(FILE *f, const unsigned char *buf, size_t len)
{
  f->write = __stdio_write;
  if (!(f->flags & F_SVB))
    f->lbf = -1;
  return __stdio_write(f, buf, len);
}

static FILE *__ofl_add(FILE *f)
{
  FILE **head = &ofl_head;
  f->next = *head;
  if (*head) (*head)->prev = f;
  *head = f;
  return f;
}

static off_t __stdio_seek(FILE *f, off_t off, int whence)
{
  return lseek(f->fd, off, whence);
}

static int __stdio_close(FILE *f)
{
  return close(f->fd);
}

static int __towrite(FILE *f)
{
  f->mode |= f->mode-1;
  if (f->flags & F_NOWR) {
    f->flags |= F_ERR;
    return EOF;
  }
  /* Clear read buffer (easier than summoning nasal demons) */
  f->rpos = f->rend = 0;

  /* Activate write through the buffer. */
  f->wpos = f->wbase = f->buf;
  f->wend = f->buf + f->buf_size;

  return 0;
}

static size_t __fwritex(const unsigned char *restrict s, size_t l, FILE *restrict f)
{
  size_t i=0;

  if (!f->wend && __towrite(f)) return 0;

  if (l > f->wend - f->wpos) return f->write(f, s, l);

  if (f->lbf >= 0) {
    /* Match /^(.*\n|)/ */
    for (i=l; i && s[i-1] != '\n'; i--);
    if (i) {
      size_t n = f->write(f, s, i);
      if (n < i) return n;
      s += i;
      l -= i;
    }
  }

  memcpy(f->wpos, s, l);
  f->wpos += l;
  return l+i;
}

static int __toread(FILE *f)
{
  f->mode |= f->mode-1;
  if (f->wpos != f->wbase) f->write(f, 0, 0);
  f->wpos = f->wbase = f->wend = 0;
  if (f->flags & F_NORD) {
    f->flags |= F_ERR;
    return EOF;
  }
  f->rpos = f->rend = f->buf + f->buf_size;
  return (f->flags & F_EOF) ? EOF : 0;
}

static int __uflow(FILE *f)
{
  unsigned char c;
  if (!__toread(f) && f->read(f, &c, 1)==1) return c;
  return EOF;
}

static int locking_getc(FILE *f)
{
  int c = getc_unlocked(f);
  return c;
}

static inline int do_getc(FILE *f)
{
  int l = f->lock;
  if (l < 0 || l)
    return getc_unlocked(f);
  return locking_getc(f);
}

static int __overflow(FILE *f, int _c)
{
  unsigned char c = _c;
  if (!f->wend && __towrite(f)) return EOF;
  if (f->wpos != f->wend && c != f->lbf) return *f->wpos++ = c;
  if (f->write(f, &c, 1)!=1) return EOF;
  return c;
}

static int locking_putc(int c, FILE *f)
{
  c = putc_unlocked(c, f);
  return c;
}

static inline int do_putc(int c, FILE *f)
{
  int l = f->lock;
  if (l < 0 || l)
    return putc_unlocked(c, f);
  return locking_putc(c, f);
}

static int __fseeko_unlocked(FILE *f, off_t off, int whence)
{
  /* Adjust relative offset for unread data in buffer, if any. */
  if (whence == SEEK_CUR && f->rend) off -= f->rend - f->rpos;

  /* Flush write buffer, and report error on failure. */
  if (f->wpos != f->wbase) {
    f->write(f, 0, 0);
    if (!f->wpos) return -1;
  }

  /* Leave writing mode */
  f->wpos = f->wbase = f->wend = 0;

  /* Perform the underlying seek. */
  if (f->seek(f, off, whence) < 0) return -1;

  /* If seek succeeded, file is seekable and we discard read buffer. */
  f->rpos = f->rend = 0;
  f->flags &= ~F_EOF;
  
  return 0;
}

static int __fseeko(FILE *f, off_t off, int whence)
{
  int result;
  result = __fseeko_unlocked(f, off, whence);
  return result;
}

static size_t __string_read(FILE *f, unsigned char *buf, size_t len)
{
  char *src = f->cookie;
  size_t k = len+256;
  char *end = memchr(src, 0, k);
  if (end) k = end-src;
  if (k < len) len = k;
  memcpy(buf, src, len);
  f->rpos = (void *)(src+len);
  f->rend = (void *)(src+k);
  f->cookie = src+k;
  return len;
}

static size_t do_read(FILE *f, unsigned char *buf, size_t len)
{
  return __string_read(f, buf, len);
}

static off_t __ftello_unlocked(FILE *f)
{
  off_t pos = f->seek(f, 0,
    (f->flags & F_APP) && f->wpos != f->wbase
    ? SEEK_END : SEEK_CUR);
  if (pos < 0) return pos;

  /* Adjust for data in buffer. */
  if (f->rend)
    pos += f->rpos - f->rend;
  else if (f->wbase)
    pos += f->wpos - f->wbase;
  return pos;
}

static off_t __ftello(FILE *f)
{
  off_t pos;
  pos = __ftello_unlocked(f);
  return pos;
}

/***************************************************************************
 * 7.21.4 Operations on files
 ***************************************************************************/

int remove(const char *path)
{
  int r = unlink(path);
  if (r==-EISDIR)
    r = rmdir(path);
  return r;
}

FILE *tmpfile(void)
{
  char s[] = "tmpfile_XXXXXX";
  int fd;
  FILE *f;
  int try;
  for (try=0; try<MAXTRIES; try++) {
    __randname(s+13);
    fd = open(s, O_RDWR|O_CREAT|O_EXCL, 0600);
    if (fd >= 0) {
      unlink(s);
      f = fdopen(fd, "w+");
      if (!f) close(fd);
      return f;
    }
  }
  return 0;
}

char *tmpnam(char *buf)
{
  static char internal[L_tmpnam];
  char s[] = "tmpnam_XXXXXX";
  int try;
  int r;
  for (try=0; try<MAXTRIES; try++) {
    __randname(s+12);
    struct stat st = {0};
    r = lstat(s, &st);
    if (r == -ENOENT) return strcpy(buf != NULL ? buf : internal, s);
  }
  return 0;
}

/***************************************************************************
 * 7.21.5 File access functions
 ***************************************************************************/

int fclose(FILE *f)
{
  int r;
  r = fflush(f);
  r |= f->close(f);

  /* Past this point, f is closed and any further explict access
   * to it is undefined. However, it still exists as an entry in
   * the open file list and possibly in the thread's locked files
   * list, if it was closed while explicitly locked. Functions
   * which process these lists must tolerate dead FILE objects
   * (which necessarily have inactive buffer pointers) without
   * producing any side effects. */

  if (f->flags & F_PERM) return r;

  FILE **head = &ofl_head;
  if (f->prev) f->prev->next = f->next;
  if (f->next) f->next->prev = f->prev;
  if (*head == f) *head = f->next;

  free(f->getln_buf);
  free(f);

  return r;
}

int fflush(FILE *f)
{
  if (!f) {
    int r = 0;
    if (__stdout_used) r |= fflush(__stdout_used);
    if (__stderr_used) r |= fflush(__stderr_used);

    for (f=ofl_head; f; f=f->next) {
      if (f->wpos != f->wbase) r |= fflush(f);
    }

    return r;
  }

  /* If writing, flush output */
  if (f->wpos != f->wbase) {
    f->write(f, 0, 0);
    if (!f->wpos) {
      return EOF;
    }
  }

  /* If reading, sync position, per POSIX */
  if (f->rpos != f->rend) f->seek(f, f->rpos-f->rend, SEEK_CUR);

  /* Clear read and write modes */
  f->wpos = f->wbase = f->wend = 0;
  f->rpos = f->rend = 0;

  return 0;
}

FILE *fopen(const char *restrict filename, const char *restrict mode)
{
  FILE *f;
  int fd;
  int flags;

  /* Check for valid initial mode character */
  if (!strchr("rwa", *mode)) {
    errno = EINVAL;
    return 0;
  }

  /* Compute the flags to pass to open() */
  flags = __fmodeflags(mode);

  fd = open(filename, flags, 0666); //sys_open(filename, flags, 0666);
  if (fd < 0) return 0;
  if (flags & O_CLOEXEC)
    fcntl(fd, F_SETFD, FD_CLOEXEC);

  f = fdopen(fd, mode);
  if (f) return f;

  close(fd);
  return 0;
}

FILE *freopen(const char *restrict filename, const char *restrict mode, FILE *restrict f)
{
  int fl = __fmodeflags(mode);
  FILE *f2;

  fflush(f);

  if (!filename) {
    if (fl&O_CLOEXEC)
      fcntl(f->fd, F_SETFD, FD_CLOEXEC);
    fl &= ~(O_CREAT|O_EXCL|O_CLOEXEC);
    if (fcntl(f->fd, F_SETFL, fl) < 0)
      goto fail;
  } else {
    f2 = fopen(filename, mode);
    if (!f2) goto fail;
    if (f2->fd == f->fd) f2->fd = -1; /* avoid closing in fclose */
    else if (dup2(f2->fd, f->fd)<0) goto fail2;

    f->flags = (f->flags & F_PERM) | f2->flags;
    f->read = f2->read;
    f->write = f2->write;
    f->seek = f2->seek;
    f->close = f2->close;

    fclose(f2);
  }

  return f;

fail2:
  fclose(f2);
fail:
  fclose(f);
  return NULL;
}

void setbuf(FILE *restrict f, char *restrict buf)
{
  setvbuf(f, buf, buf != NULL ? _IOFBF : _IONBF, BUFSIZ);
}

int setvbuf(FILE *restrict f, char *restrict buf, int type, size_t size)
{
  f->lbf = EOF;

  if (type == _IONBF) {
    f->buf_size = 0;
  } else {
    if (buf && size >= UNGET) {
      f->buf = (void *)(buf + UNGET);
      f->buf_size = size - UNGET;
    }
    if (type == _IOLBF && f->buf_size)
      f->lbf = '\n';
  }

  f->flags |= F_SVB;

  return 0;
}

/***************************************************************************
 * 7.21.6 Formatted input/output functions
 ***************************************************************************/

int fprintf(FILE *restrict f, const char *restrict fmt, ...)
{
  int ret;
  va_list ap;
  va_start(ap, fmt);
  ret = vfprintf(f, fmt, ap);
  va_end(ap);
  return ret;
}

int fscanf(FILE *restrict f, const char *restrict fmt, ...)
{
  int ret;
  va_list ap;
  va_start(ap, fmt);
  ret = vfscanf(f, fmt, ap);
  va_end(ap);
  return ret;
}

int printf(const char *restrict fmt, ...)
{
  int ret;
  va_list ap;
  va_start(ap, fmt);
  ret = vfprintf(stdout, fmt, ap);
  va_end(ap);
  return ret;
}

int scanf(const char *restrict fmt, ...)
{
  int ret;
  va_list ap;
  va_start(ap, fmt);
  ret = vscanf(fmt, ap);
  va_end(ap);
  return ret;
}

int snprintf(char *restrict s, size_t n, const char *restrict fmt, ...)
{
  int ret;
  va_list ap;
  va_start(ap, fmt);
  ret = vsnprintf(s, n, fmt, ap);
  va_end(ap);
  return ret;
}

int sprintf(char *restrict s, const char *restrict fmt, ...)
{
  int ret;
  va_list ap;
  va_start(ap, fmt);
  ret = vsprintf(s, fmt, ap);
  va_end(ap);
  return ret;
}

int sscanf(const char *restrict s, const char *restrict fmt, ...)
{
  int ret;
  va_list ap;
  va_start(ap, fmt);
  ret = vsscanf(s, fmt, ap);
  va_end(ap);
  return ret;
}


// TODO
int vfprintf(FILE *restrict f, const char *restrict fmt, va_list ap)
{
  return 0;
}

// TODO
int vfscanf(FILE *restrict f, const char *restrict fmt, va_list ap)
{
}

// TODO
int vsnprintf(char *restrict s, size_t n, const char *restrict fmt, va_list ap)
{
}

int vsprintf(char *restrict s, const char *restrict fmt, va_list ap)
{
  return vsnprintf(s, INT_MAX, fmt, ap);
}

int vsscanf(const char *restrict s, const char *restrict fmt, va_list ap)
{
  FILE f = {
    .read = do_read,
    .buf = (void *)s,
    .cookie = (void *)s,
  };
  return vfscanf(&f, fmt, ap);
}

/***************************************************************************
 * 7.21.7 Character input/output functions
 ***************************************************************************/

int fgetc(FILE *f)
{
  return do_getc(f);
}

char *fgets(char *restrict s, int n, FILE *restrict f)
{
  char *p = s;
  unsigned char *z;
  size_t k;
  int c;

  if (n--<=1) {
    f->mode |= f->mode-1;
    if (n) return 0;
    *s = 0;
    return s;
  }

  while (n) {
    if (f->rpos != f->rend) {
      z = memchr(f->rpos, '\n', f->rend - f->rpos);
      k = z != NULL ? z - f->rpos + 1 : f->rend - f->rpos;
      k = MIN(k, n);
      memcpy(p, f->rpos, k);
      f->rpos += k;
      p += k;
      n -= k;
      if (z || !n) break;
    }
    if ((c = getc_unlocked(f)) < 0) {
      if (p==s || !feof(f)) s = 0;
      break;
    }
    n--;
    if ((*p++ = c) == '\n') break;
  }
  if (s) *p = 0;

  return s;
}

int fputc(int c, FILE *f)
{
  return do_putc(c, f);
}

int getc(FILE *f)
{
  return do_getc(f);
}

int getchar(void)
{
  return do_getc(stdin);
}

int putc(int c, FILE *f)
{
  return do_putc(c, f);
}

int putchar(int c)
{
  return do_putc(c, stdout);
}

int puts(const char *s)
{
  int r;
  r = -(fputs(s, stdout) < 0 || putc_unlocked('\n', stdout) < 0);
  return r;
}

int ungetc(int c, FILE *f)
{
  if (c == EOF) return c;

  if (!f->rpos) __toread(f);
  if (!f->rpos || f->rpos <= f->buf - UNGET) {
    return EOF;
  }

  *--f->rpos = c;
  f->flags &= ~F_EOF;
  return c;
}

/***************************************************************************
 * 7.21.8 Direct input/output functions
 ***************************************************************************/

size_t fread(void *restrict destv, size_t size, size_t nmemb, FILE *restrict f)
{
  unsigned char *dest = destv;
  size_t len = size*nmemb, l = len, k;
  if (!size) nmemb = 0;

  f->mode |= f->mode-1;

  if (f->rpos != f->rend) {
    /* First exhaust the buffer. */
    k = MIN(f->rend - f->rpos, l);
    memcpy(dest, f->rpos, k);
    f->rpos += k;
    dest += k;
    l -= k;
  }
  
  /* Read the remainder directly */
  for (; l; l-=k, dest+=k) {
    k = __toread(f) ? 0 : f->read(f, dest, l);
    if (!k) {
      return (len-l)/size;
    }
  }

  return nmemb;
}

size_t fwrite(const void *restrict src, size_t size, size_t nmemb, FILE *restrict f)
{
  size_t k, l = size*nmemb;
  if (!size) nmemb = 0;
  k = __fwritex(src, l, f);
  return k==l ? nmemb : k/size;
}

/***************************************************************************
 * 7.21.9 File positioning functions
 ***************************************************************************/


int fgetpos(FILE *restrict f, fpos_t *restrict pos)
{
  off_t off = __ftello(f);
  if (off < 0) return -1;
  *(long long *)pos = off;
  return 0;
}

int fseek(FILE *f, long off, int whence)
{
  return __fseeko(f, off, whence);
}

int fsetpos(FILE *f, const fpos_t *pos)
{
  return __fseeko(f, *(const long long *)pos, SEEK_SET);
}


long ftell(FILE *f)
{
  off_t pos = __ftello(f);
  if (pos > LONG_MAX) {
    errno = EOVERFLOW;
    return -1;
  }
  return pos;
}

void rewind(FILE *f)
{
  __fseeko_unlocked(f, 0, SEEK_SET);
  f->flags &= ~F_ERR;
}


/***************************************************************************
 * 7.21.10 Error-handling functions
 ***************************************************************************/

void clearerr(FILE *f)
{
  f->flags &= ~(F_EOF|F_ERR);
}


int feof(FILE *f)
{
  int ret = !!(f->flags & F_EOF);
  return ret;
}

int ferror(FILE *f)
{
  int ret = !!(f->flags & F_ERR);
  return ret;
}

void perror(const char *msg)
{
  FILE *f = stderr;
  char *errstr = strerror(errno);

  /* Save stderr's orientation and encoding rule, since perror is not
   * permitted to change them. */
  void *old_locale = f->locale;
  int old_mode = f->mode;
  
  if (msg && *msg) {
    fwrite(msg, strlen(msg), 1, f);
    fputc(':', f);
    fputc(' ', f);
  }
  fwrite(errstr, strlen(errstr), 1, f);
  fputc('\n', f);

  f->mode = old_mode;
  f->locale = old_locale;
}

/***************************************************************************
 * POSIX
 ***************************************************************************/

FILE *fdopen(int fd, const char *mode)
{
  FILE *f;
  //struct winsize wsz;

  /* Check for valid initial mode character */
  if (!strchr("rwa", *mode)) {
    errno = EINVAL;
    return 0;
  }

  /* Allocate FILE+buffer or fail */
  if (!(f=malloc(sizeof *f + UNGET + BUFSIZ))) return 0;

  /* Zero-fill only the struct, not the buffer */
  memset(f, 0, sizeof *f);

  /* Impose mode restrictions */
  if (!strchr(mode, '+')) f->flags = (*mode == 'r') ? F_NOWR : F_NORD;

  /* Apply close-on-exec flag */
  if (strchr(mode, 'e')) fcntl(fd, F_SETFD, FD_CLOEXEC);

  /* Set append mode on fd if opened for append */
  if (*mode == 'a') {
    int flags = fcntl (fd, F_GETFL);
    if (!(flags & O_APPEND))
      fcntl(fd, F_SETFL, flags | O_APPEND);
    f->flags |= F_APP;
  }

  f->fd = fd;
  f->buf = (unsigned char *)f + sizeof *f + UNGET;
  f->buf_size = BUFSIZ;

  /* Activate line buffered mode for terminals */
  f->lbf = EOF;
  //if (!(f->flags & F_NOWR) && !ioctl(fd, TIOCGWINSZ, &wsz))
  //  f->lbf = '\n';

  /* Initialize op ptrs. No problem if some are unneeded. */
  f->read = __stdio_read;
  f->write = __stdio_write;
  f->seek = __stdio_seek;
  f->close = __stdio_close;

  //if (!libc.threaded) f->lock = -1;

  /* Add new FILE to open file list */
  return __ofl_add(f);
}

int fileno(FILE *f)
{
  int fd = f->fd;
  if (fd < 0) {
    errno = EBADF;
    return -1;
  }
  return fd;
}



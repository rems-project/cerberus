#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/uio.h>
#include "stdio.h"

#define MIN(a,b) ((a)<(b) ? (a) : (b))

// No locks
#define FLOCK(f)
#define FUNLOCK(f)

int putchar(int c)
{
  return printf("%c", c);
}
int puts(const char *s)
{
  return printf("%s", s);
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

#define UNGET 8

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

static FILE *ofl_head;
static volatile int ofl_lock[1];

FILE *volatile __stdin_used;
FILE *volatile __stdout_used;
FILE *volatile __stderr_used;

FILE **__ofl_lock()
{
  //LOCK(ofl_lock);
  return &ofl_head;
}

void __ofl_unlock()
{
  //UNLOCK(ofl_lock);
}

size_t __stdio_read(FILE *f, unsigned char *buf, size_t len)
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

size_t __stdio_write(FILE *f, const unsigned char *buf, size_t len)
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

static FILE *__ofl_add(FILE *f)
{
  FILE **head = __ofl_lock();
  f->next = *head;
  if (*head) (*head)->prev = f;
  *head = f;
  __ofl_unlock();
  return f;
}

off_t __stdio_seek(FILE *f, off_t off, int whence)
{
  off_t ret;
#ifdef SYS__llseek
  if (llseek(f->fd, off>>32, off, &ret, whence)<0)
    ret = -1;
#else
  ret = lseek(f->fd, off, whence);
#endif
  return ret;
}

int __stdio_close(FILE *f)
{
  return close(f->fd);
}

FILE *__fdopen(int fd, const char *mode)
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

  f = __fdopen(fd, mode);
  if (f) return f;

  close(fd);
  return 0;
}


int fclose(FILE *f)
{
  int r;
  
  FLOCK(f);
  r = fflush(f);
  r |= f->close(f);
  FUNLOCK(f);

  /* Past this point, f is closed and any further explict access
   * to it is undefined. However, it still exists as an entry in
   * the open file list and possibly in the thread's locked files
   * list, if it was closed while explicitly locked. Functions
   * which process these lists must tolerate dead FILE objects
   * (which necessarily have inactive buffer pointers) without
   * producing any side effects. */

  if (f->flags & F_PERM) return r;

  //__unlist_locked_file(f);

  FILE **head = __ofl_lock();
  if (f->prev) f->prev->next = f->next;
  if (f->next) f->next->prev = f->prev;
  if (*head == f) *head = f->next;
  __ofl_unlock();

  free(f->getln_buf);
  free(f);

  return r;
}

int __towrite(FILE *f)
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

size_t __fwritex(const unsigned char *restrict s, size_t l, FILE *restrict f)
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

size_t fwrite(const void *restrict src, size_t size, size_t nmemb, FILE *restrict f)
{
  size_t k, l = size*nmemb;
  if (!size) nmemb = 0;
  FLOCK(f);
  k = __fwritex(src, l, f);
  FUNLOCK(f);
  return k==l ? nmemb : k/size;
}

int __toread(FILE *f)
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

size_t fread(void *restrict destv, size_t size, size_t nmemb, FILE *restrict f)
{
  unsigned char *dest = destv;
  size_t len = size*nmemb, l = len, k;
  if (!size) nmemb = 0;

  FLOCK(f);

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
      FUNLOCK(f);
      return (len-l)/size;
    }
  }

  FUNLOCK(f);
  return nmemb;
}

int fflush(FILE *f)
{
  if (!f) {
    int r = 0;
    if (__stdout_used) r |= fflush(__stdout_used);
    if (__stderr_used) r |= fflush(__stderr_used);

    for (f=*__ofl_lock(); f; f=f->next) {
      FLOCK(f);
      if (f->wpos != f->wbase) r |= fflush(f);
      FUNLOCK(f);
    }
    __ofl_unlock();

    return r;
  }

  FLOCK(f);

  /* If writing, flush output */
  if (f->wpos != f->wbase) {
    f->write(f, 0, 0);
    if (!f->wpos) {
      FUNLOCK(f);
      return EOF;
    }
  }

  /* If reading, sync position, per POSIX */
  if (f->rpos != f->rend) f->seek(f, f->rpos-f->rend, SEEK_CUR);

  /* Clear read and write modes */
  f->wpos = f->wbase = f->wend = 0;
  f->rpos = f->rend = 0;

  FUNLOCK(f);
  return 0;
}


int ferror(FILE *f)
{
  FLOCK(f);
  int ret = !!(f->flags & F_ERR);
  FUNLOCK(f);
  return ret;
}


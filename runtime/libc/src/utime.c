#include <time.h>
#include <sys/stat.h>
#include <fcntl.h>
#include "utime.h"

int utime(const char *path, const struct utimbuf *times)
{
  if (times) {
    struct timespec ts [2];
    ts[0].tv_sec = times->actime;
    ts[1].tv_sec = times->modtime;
    return utimensat(AT_FDCWD, path, ts, 0);
  }
  return utimensat(AT_FDCWD, path, 0, 0);
}

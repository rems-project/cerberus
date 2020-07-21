#ifndef _DIRENT_H_
#define _DIRENT_H_

#include <stdint.h>
#include <limits.h>
#include <sys/types.h>

// NOTE: this is implementation-defined
// SibylFS uses an integer as a `directory descriptor`
typedef int DIR;

struct dirent {
  int  d_namlen; // NOTE: This is not POSIX
  char d_name[NAME_MAX+1];
};

int alphasort(const struct dirent **, const struct dirent **);
int closedir(DIR *);
int dirfd(DIR *);
DIR *fdopendir(int);
DIR *opendir(const char *);
struct dirent *readdir(DIR *);
int readdir_r(DIR *restrict, struct dirent *restrict, struct dirent **restrict);
void rewinddir(DIR *);
int scandir(const char *, struct dirent ***,
            int (*)(const struct dirent *),
            int (*)(const struct dirent **,
            const struct dirent **));

#endif

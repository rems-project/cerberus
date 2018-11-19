#ifndef _SYS_STAT_H_
#define _SYS_STAT_H_

// TODO

#include <sys/types.h>

struct timespec
{
  time_t  tv_sec;
  long    tv_nsec;
};

// http://pubs.opengroup.org/onlinepubs/9699919799/
struct stat {
  dev_t           st_dev;
  ino_t           st_ino;
  mode_t          st_mode;
  nlink_t         st_nlink;
  uid_t           st_uid;
  gid_t           st_gid;
  dev_t           st_rdev;
  off_t           st_size;
  struct timespec st_atim;
  struct timespec st_mtim;
  struct timespec st_ctim;
  blksize_t       st_blksize;
  blkcnt_t        st_block;
};

// int    chmod(const char *, mode_t);
int    fchmod(int, mode_t);
// int    fchmodat(int, const char *, mode_t, int);
int    fstat(int, struct stat *);
// int    fstatat(int, const char *restrict, struct stat *restrict, int);
// int    futimens(int, const struct timespec [2]);
int    lstat(const char *restrict, struct stat *restrict);
int    mkdir(const char *, mode_t);
// int    mkdirat(int, const char *, mode_t);
// int    mkfifo(const char *, mode_t);
// int    mkfifoat(int, const char *, mode_t);
// int    mknod(const char *, mode_t, dev_t);
// int    mknodat(int, const char *, mode_t, dev_t);
int    stat(const char *restrict, struct stat *restrict);
// mode_t umask(mode_t);
// int    utimensat(int, const char *, const struct timespec [2], int);


// TODO this should be a 1-arg macro
#define S_ISDIR(m) __cerbvar_S_ISDIR(m)
#define S_ISLNK(m) __cerbvar_S_ISLNK(m)

#endif

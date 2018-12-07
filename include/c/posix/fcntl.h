#ifndef _FCNTL_H_
#define _FCNTL_H_

// fctnl flag operations (int)
// taken from Linux include/uapi/asm-generic/fcntl.h
#define F_DUPFD         0
#define F_GETFD         1
#define F_SETFD         2
#define F_GETFL         3
#define F_SETFL         4
#define F_GETLK         5
#define F_SETLK         6
#define F_SETLKW        7
#define F_GETOWN        8
#define F_SETOWN        9

#define F_DUPFD_CLOEXEC 1

#define F_RDLCK         0
#define F_UNLCK         1
#define F_WRLCK_        2

// open flags (int)
// taken from fs_spec.lem
#define O_EXEC        00000000001
#define O_RDONLY      00000000002
#define O_WRONLY      00000000004
#define O_ACCMODE     00000000006
#define O_RDWR        00000000010
#define O_SEARCH      00000000020
#define O_CREAT       00000000040
#define O_EXCL        00000000100
#define O_NOCTTY      00000000200
#define O_TRUNC       00000000400
#define O_APPEND      00000001000
#define O_NONBLOCK    00000002000
#define O_RSYNC       00000004000
#define O_SYNC        00000010000
#define O_DSYNC       00000020000
#define O_DIRECTORY   00000040000
#define O_NOFOLLOW    00000100000
#define O_CLOEXEC     00000200000
#define O_TTY_INIT    00000400000

#include <sys/types.h>

struct flock {
  short  l_type;
  short  l_whence;
  off_t  l_start;
  off_t  l_len;
  pid_t  l_pid;
};

int  open(const char *, int, ...);
int  fcntl(int, int, ...);

#endif

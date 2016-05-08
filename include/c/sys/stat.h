#ifndef _SYS_STAT_H_
#define	_SYS_STAT_H_

struct stat {
  dev_t st_dev;
  ino_t st_ino;
  mode_t st_mode;
  nlink_t st_nlink;
  uid_t st_uid;
  gid_t st_gid;
  dev_t st_rdev;
  off_t st_size;
  time_t st_atime, st_mtime, st_ctime;
  blksize_t st_blksize;
  blkcnt_t st_blocks;
};


int fstat(int fildes, struct stat *buf);

#else
#endif

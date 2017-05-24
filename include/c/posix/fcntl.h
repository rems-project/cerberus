

#define F_DUPFD         __cerbvar_F_DUPFD
#define F_DUPFD_CLOEXEC __cerbvar_F_DUPFD_CLOEXEC
#define F_GETFD         __cerbvar_F_GETFD
#define F_SETFD         __cerbvar_F_SETFD
#define F_GETFL         __cerbvar_F_GETFL
#define F_SETFL         __cerbvar_F_SETFL
#define F_GETLK         __cerbvar_F_GETLK
#define F_SETLK         __cerbvar_F_SETLK
#define F_SETLKW        __cerbvar_F_SETLKW
#define F_GETOWN        __cerbvar_F_GETOWN
#define F_SETOWN        __cerbvar_F_SETOWN


#define F_RDLCK __cerbvar_F_RDLCK
#define F_UNLCK __cerbvar_F_UNLCK
#define F_WRLCK __cerbvar_F_WRLCK


#define O_CLOEXEC   __cerbvar_O_CLOEXEC
#define O_CREAT     __cerbvar_O_CREAT
#define O_DIRECTORY __cerbvar_O_DIRECTORY
#define O_EXCL      __cerbvar_O_EXCL
#define O_NOCTTY    __cerbvar_O_NOCTTY
#define O_NOFOLLOW  __cerbvar_O_NOFOLLOW
#define O_TRUNC     __cerbvar_O_TRUNC
#define O_TTY_INIT  __cerbvar_O_TTY_INIT


#define O_APPEND   __cerbvar_O_APPEND
#define O_DSYNC    __cerbvar_O_DSYNC
#define O_NONBLOCK __cerbvar_O_NONBLOCK
#define O_RSYNC    __cerbvar_O_RSYNC
#define O_SYNC     __cerbvar_O_SYNC


#define O_ACCMODE  __cerbvar_O_ACCMODE


#define O_EXEC     __cerbvar_O_EXEC
#define O_RDONLY   __cerbvar_O_RDONLY
#define O_RDWR     __cerbvar_O_RDWR
#define O_SEARCH   __cerbvar_O_SEARCH
#define O_WRONLY   __cerbvar_O_WRONLY


int  open(const char *, int, ...);
int  fcntl(int, int, ...);

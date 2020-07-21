#ifndef _POSIX_ERRNO_H_
#define _POSIX_ERRNO_H_

// Distinct positive values with type int

#define E2BIG           __cerbvar_E2BIG
#define EACCES          __cerbvar_EACCES
#define EADDRINUSE      __cerbvar_EADDRINUSE
#define EADDRNOTAVAIL   __cerbvar_EADDRNOTAVAIL
#define EAFNOSUPPORT    __cerbvar_EAFNOSUPPORT
#define EAGAIN          __cerbvar_EAGAIN
#define EALREADY        __cerbvar_EALREADY
#define EBADF           __cerbvar_EBADF
#define EBADMSG         __cerbvar_EBADMSG
#define EBUSY           __cerbvar_EBUSY
#define ECANCELED       __cerbvar_ECANCELED
#define ECHILD          __cerbvar_ECHILD
#define ECONNABORTED    __cerbvar_ECONNABORTED
#define ECONNREFUSED    __cerbvar_ECONNREFUSED
#define ECONNRESET      __cerbvar_ECONNRESET
#define EDEADLK         __cerbvar_EDEADLK
#define EDESTADDRREQ    __cerbvar_EDESTADDRREQ
#ifndef EDOM // defined in ISO C
#define EDOM            __cerbvar_EDOM
#endif
#define EDQUOT          __cerbvar_EDQUOT
#define EEXIST          __cerbvar_EEXIST
#define EFAULT          __cerbvar_EFAULT
#define EFBIG           __cerbvar_EFBIG
#define EHOSTUNREACH    __cerbvar_EHOSTUNREACH
#define EIDRM           __cerbvar_EIDRM
#ifndef EILSEQ // defined in ISO C
#define EILSEQ          __cerbvar_EILSEQ
#endif
#define EINPROGRESS     __cerbvar_EINPROGRESS
#define EINTR           __cerbvar_EINTR
#define EINVAL          __cerbvar_EINVAL
#define EIO             __cerbvar_EIO
#define EISCONN         __cerbvar_EISCONN
#define EISDIR          __cerbvar_EISDIR
#define ELOOP           __cerbvar_ELOOP
#define EMFILE          __cerbvar_EMFILE
#define EMLINK          __cerbvar_EMLINK
#define EMSGSIZE        __cerbvar_EMSGSIZE
#define EMULTIHOP       __cerbvar_EMULTIHOP
#define ENAMETOOLONG    __cerbvar_ENAMETOOLONG
#define ENETDOWN        __cerbvar_ENETDOWN
#define ENETRESET       __cerbvar_ENETRESET
#define ENETUNREACH     __cerbvar_ENETUNREACH
#define ENFILE          __cerbvar_ENFILE
#define ENOBUFS         __cerbvar_ENOBUFS
#define ENODATA         __cerbvar_ENODATA
#define ENODEV          __cerbvar_ENODEV
#define ENOENT          __cerbvar_ENOENT
#define ENOEXEC         __cerbvar_ENOEXEC
#define ENOLCK          __cerbvar_ENOLCK
#define ENOLINK         __cerbvar_ENOLINK
#define ENOMEM          __cerbvar_ENOMEM
#define ENOMSG          __cerbvar_ENOMSG
#define ENOPROTOOPT     __cerbvar_ENOPROTOOPT
#define ENOSPC          __cerbvar_ENOSPC
#define ENOSR           __cerbvar_ENOSR
#define ENOSTR          __cerbvar_ENOSTR
#define ENOSYS          __cerbvar_ENOSYS
#define ENOTCONN        __cerbvar_ENOTCONN
#define ENOTDIR         __cerbvar_ENOTDIR
#define ENOTEMPTY       __cerbvar_ENOTEMPTY
#define ENOTRECOVERABLE __cerbvar_ENOTRECOVERABLE
#define ENOTSOCK        __cerbvar_ENOTSOCK
#define ENOTSUP         __cerbvar_ENOTSUP
#define ENOTTY          __cerbvar_ENOTTY
#define ENXIO           __cerbvar_ENXIO
#define EOPNOTSUPP      __cerbvar_EOPNOTSUPP
#define EOVERFLOW       __cerbvar_EOVERFLOW
#define EOWNERDEAD      __cerbvar_EOWNERDEAD
#define EPERM           __cerbvar_EPERM
#define EPIPE           __cerbvar_EPIPE
#define EPROTO          __cerbvar_EPROTO
#define EPROTONOSUPPORT __cerbvar_EPROTONOSUPPORT
#define EPROTOTYPE      __cerbvar_EPROTOTYPE
#ifndef ERANGE // defined in ISO C
#define ERANGE          __cerbvar_ERANGE
#endif
#define EROFS           __cerbvar_EROFS
#define ESPIPE          __cerbvar_ESPIPE
#define ESRCH           __cerbvar_ESRCH
#define ESTALE          __cerbvar_ESTALE
#define ETIME           __cerbvar_ETIME
#define ETIMEDOUT       __cerbvar_ETIMEDOUT
#define ETXTBSY         __cerbvar_ETXTBSY
#define EWOULDBLOCK     __cerbvar_EWOULDBLOCK
#define EXDEV           __cerbvar_EXDEV

#endif

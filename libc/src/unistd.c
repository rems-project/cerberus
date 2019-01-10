#include <stdio.h>
#include <string.h>
#include "unistd.h"

// NOTE: HACK
#define __lctrans_cur(x) x
#define FLOCK(f)
#define FUNLOCK(f)

// TODO: isatty
int isatty (int fd)
{
  return 0;//return (fd == 1 || fd == 2);
}

static void __procfdname(char *buf, unsigned fd)
{
  unsigned i, j;
  for (i=0; (buf[i] = "/proc/self/fd/"[i]); i++);
  if (!fd) {
    buf[i] = '0';
    buf[i+1] = 0;
    return;
  }
  for (j=fd; j; j/=10, i++);
  buf[i] = 0;
  for (; fd; fd/=10) buf[--i] = '0' + fd%10;
}

int fchown(int fd, uid_t uid, gid_t gid)
{
  /*
  int ret = __syscall(SYS_fchown, fd, uid, gid);
  if (ret != -EBADF || __syscall(SYS_fcntl, fd, F_GETFD) < 0)
    return __syscall_ret(ret);
  */

  char buf[15+3*sizeof(int)];
  __procfdname(buf, fd);
  return chown(buf, uid, gid);
}


int opterr = 1,   /* if error message should be printed */
  optind = 1,   /* index into parent argv vector */
  optopt,     /* character checked for validity */
  optreset;   /* reset getopt */
char  *optarg;    /* argument associated with option */

#undef  BADCH
#define BADCH (int)'?'
#undef  BADARG
#define BADARG  (int)':'
#undef  EMSG
#define EMSG  ""

  static char *progname;
  static char *place = EMSG;    /* option letter processing */

/*
 * getopt --
 *  Parse argc/argv argument vector.
 *
 * PUBLIC: #ifndef HAVE_GETOPT
 * PUBLIC: int getopt __P((int, char * const *, const char *));
 * PUBLIC: #endif
 */
int
getopt(int nargc, char * const * nargv, const char *ostr)
{
  char *oli;        /* option letter list index */

  if (!progname) {
    progname = *nargv;
    /*
    if ((progname = *nargv) == NULL)
                  progname = *nargv;
          else
                  ++progname;
    */
  }

  if (optreset || !*place) {    /* update scanning pointer */
    optreset = 0;
    if (optind >= nargc || *(place = nargv[optind]) != '-') {
      place = EMSG;
      return (EOF);
    }
    if (place[1] && *++place == '-') {  /* found "--" */
      ++optind;
      place = EMSG;
      return (EOF);
    }
  }         /* option letter okay? */
  if ((optopt = (int)*place++) == (int)':' ||
      !(oli = strchr(ostr, optopt))) {
    /*
     * if the user didn't specify '-' as an option,
     * assume it means EOF.
     */
    if (optopt == (int)'-')
      return (EOF);
    if (!*place)
      ++optind;
    if (opterr && *ostr != ':')
      (void)printf(/*stderr,*/
          "%s: illegal option -- %c\n", progname, optopt);
    return (BADCH);
  }
  if (*++oli != ':') {      /* don't need argument */
    optarg = NULL;
    if (!*place)
      ++optind;
  }
  else {          /* need an argument */
    if (*place)     /* no white space */
      optarg = place;
    else if (nargc <= ++optind) { /* no arg */
      place = EMSG;
      if (*ostr == ':')
        return (BADARG);
      if (opterr)
        (void)printf(
            "%s: option requires an argument -- %c\n",
            progname, optopt);
      return (BADCH);
    }
    else        /* white space */
      optarg = nargv[optind];
    place = EMSG;
    ++optind;
  }
  return (optopt);      /* dump back option letter */
}



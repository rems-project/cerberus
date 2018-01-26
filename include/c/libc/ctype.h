#ifndef	_CTYPE_H_
#define	_CTYPE_H_

// TODO: the following implementation is only for "C" locale.

int isblank(int c) {
  return c == ' ' || c == '\t';
}

int iscntrl(int c) {
  return (unsigned)c < 0x20 || c == 0x7f;
}

int isdigit(int c) {
  return (unsigned)c-'0' < 10;
}

int isgraph(int c) {
  return (unsigned)c-0x21 < 0x5e;
}

int isprint(int c) {
  return (unsigned)c-0x20 < 0x5f;
}

int isspace(int c) {
  return c == ' ' || c == '\f' || c == '\n' || c == '\r' || c == '\t' || c == '\v';
}

int islower(int c) {
  if (iscntrl(c) || isdigit(c) || isgraph(c) || isspace(c))
    return 0;
  return (unsigned)c-'a' < 26;
}

int isupper(int c) {
  if (iscntrl(c) || isdigit(c) || isgraph(c) || isspace(c))
    return 0;
  return (unsigned)c-'A' < 26;
}

int isalpha(int c) {
  return isupper(c) || islower(c);
}

int isalnum(int c) {
  return isalpha(c) || isdigit(c);
}

int ispunct(int c) {
  if (isspace(c) || isalnum(c))
    return 0;
  return isgraph(c);
}

int isxdigit(int c) {
  return isdigit(c) || ((unsigned)c|32)-'a' < 6;
}

int tolower(int c) {
  if (isupper(c)) return c | 32;
  return c;
}

int toupper(int c) {
  if (islower(c)) return c & 0x5f;
  return c;
}

#else
#endif

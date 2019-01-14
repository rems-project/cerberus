// from https://git.musl-libc.org/cgit/libc-testsuite/

#define _BSD_SOURCE
#include <stdio.h>
#include <string.h>

/* r = place to store result
 * f = function call to test (or any expression)
 * x = expected result
 * m = message to print on failure (with formats for r & x)
**/

#define TEST(r, f, x, m) ( \
((r) = (f)) == (x) || \
(printf(__FILE__ ":%d: %s failed (" m ")\n", __LINE__, #f, r, x), err++, 0) )

#define TEST_S(s, x, m) ( \
!strcmp((s),(x)) || \
(printf(__FILE__ ":%d: [%s] != [%s] (%s)\n", __LINE__, s, x, m), err++, 0) )

int main(void)
{
  char b[32];
  char *s;
  int i;
  int err=0;

  b[16]='a'; b[17]='b'; b[18]='c'; b[19]=0;
  TEST(s, strcpy(b, b+16), b, "wrong return %p != %p");
  TEST_S(s, "abc", "strcpy gave incorrect string");
  TEST(s, strcpy(b+1, b+16), b+1, "wrong return %p != %p");
  TEST_S(s, "abc", "strcpy gave incorrect string");
  TEST(s, strcpy(b+2, b+16), b+2, "wrong return %p != %p");
  TEST_S(s, "abc", "strcpy gave incorrect string");
  TEST(s, strcpy(b+3, b+16), b+3, "wrong return %p != %p");
  TEST_S(s, "abc", "strcpy gave incorrect string");

  TEST(s, strcpy(b+1, b+17), b+1, "wrong return %p != %p");
  TEST_S(s, "bc", "strcpy gave incorrect string");
  TEST(s, strcpy(b+2, b+18), b+2, "wrong return %p != %p");
  TEST_S(s, "c", "strcpy gave incorrect string");
  TEST(s, strcpy(b+3, b+19), b+3, "wrong return %p != %p");
  TEST_S(s, "", "strcpy gave incorrect string");

  TEST(s, memset(b, 'x', sizeof b), b, "wrong return %p != %p");
  TEST(s, strncpy(b, "abc", sizeof b - 1), b, "wrong return %p != %p");
  TEST(i, memcmp(b, "abc\0\0\0\0", 8), 0, "strncpy fails to zero-pad dest");
  TEST(i, b[sizeof b - 1], 'x', "strncpy overruns buffer when n > strlen(src)");

  b[3] = 'x'; b[4] = 0;
  strncpy(b, "abc", 3);
  TEST(i, b[2], 'c', "strncpy fails to copy last byte: %hhu != %hhu");
  TEST(i, b[3], 'x', "strncpy overruns buffer to null-terminate: %hhu != %hhu");

  TEST(i, !strncmp("abcd", "abce", 3), 1, "strncmp compares past n");
  TEST(i, !!strncmp("abc", "abd", 3), 1, "strncmp fails to compare n-1st byte");

  strcpy(b, "abc");
  TEST(s, strncat(b, "123456", 3), b, "%p != %p");
  TEST(i, b[6], 0, "strncat failed to null-terminate (%d)");
  TEST_S(s, "abc123", "strncat gave incorrect string");

  strcpy(b, "aaababccdd0001122223");
  TEST(s, strchr(b, 'b'), b+3, "%p != %p");
  TEST(s, strrchr(b, 'b'), b+5, "%p != %p");
  TEST(i, strspn(b, "abcd"), 10, "%d != %d");
  strcspn(b, "0123");
  TEST(i, strcspn(b, "0123"), 10, "%d != %d");
  TEST(s, strpbrk(b, "0123"), b+10, "%d != %d");

  strcpy(b, "abc   123; xyz; foo");
  TEST(s, strtok(b, " "), b, "%p != %p");
  TEST_S(s, "abc", "strtok result");

  TEST(s, strtok(NULL, ";"), b+4, "%p != %p");
  TEST_S(s, "  123", "strtok result");

  TEST(s, strtok(NULL, "; "), b+11, "%p != %p");
  TEST_S(s, "xyz", "strtok result");

  TEST(s, strtok(NULL, " ;"), b+16, "%p != %p");
  TEST_S(s, "foo", "strtok result");

  return err;
}


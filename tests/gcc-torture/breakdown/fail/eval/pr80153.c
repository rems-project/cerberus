#include "cerberus.h"
/* PR tree-optimization/80153 */

void check (int, int, int) ;
void check (int c, int c2, int val)
{
  if (!val) {
    __builtin_abort();
  }
}

static const char *buf;
static int l, i;

void _fputs(const char *str)  ;
void _fputs(const char *str)
{
  buf = str;
  i = 0;
  l = __builtin_strlen(buf);
}

char _fgetc() ;
char 
_fgetc (void)
{
  char val = buf[i];
  i++;
  if (i > l)
    return -1;
  else
    return val;
}

static const char *string = "oops!\n";

int main(void)
{
  int i;
  int c;

  _fputs(string);

  for (i = 0; i < __builtin_strlen(string); i++) {
    c = _fgetc();
    check(c, string[i], c == string[i]);
  }

  return 0;
}

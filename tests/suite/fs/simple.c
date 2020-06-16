/* Simple use of the filesystem. Identifies UB in musl:
 * https://git.musl-libc.org/cgit/musl/commit/src/stdio?id=b287cd745c2243f8e5114331763a5a9813b5f6ee
 */
#include <stdio.h>
int main() {
  FILE  * f = fopen("foo.txt", "w+");
  if (!f) return 1;
  fprintf(f, "hello, world\n");
  char c;
  rewind(f);
  fscanf(f, "%c", &c);
  assert(c == 'h');
  return 0;
}

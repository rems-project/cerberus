/* STD §6.8#3: the initialisations of a declaration are done in the order that its
   declarators appear, including in the declaration of a for statement (§6.8.5.3#1) */
int printf(const char *, ...);
int main(void)
{
  int n = 0, r1 = 0, r2 = 0;
  /* the side effects of the initialisers happen in order: a = 1, b = 2, c = 3 */
  for (int a = ++n, b = ++n, c = ++n; !r1; )
    r1 = a * 100 + b * 10 + c;
  /* each initialiser can use the objects declared before it: a = 4, b = 5, c = 6 */
  for (int a = 4, b = a + 1, c = b + 1; !r2; )
    r2 = a * 100 + b * 10 + c;
  printf("%d\n", r1 * 1000 + r2);
}

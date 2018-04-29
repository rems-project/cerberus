void my_memcpy(void *dest, void *src, int n) {
  unsigned char *p = dest, *q = src, *end = p + n;
  while (p < end) // end may be end-of-array
    *p++ = *q++;
}
int main() {
  struct S { short x; short *r; } s = { 10, &s.x }, s2;
  my_memcpy(&s2, &s, sizeof(struct S));
  return *(s2.r);
}

#define PORTBASE 0x40000000
unsigned int volatile * const port = 
  (unsigned int *) PORTBASE;
int main() {
  unsigned int value = 0;
  // on systems where PORTBASE is a legal non-stack/heap 
  // address, does this have defined behaviour?
  *port = value; /* write to port */
  value = *port; /* read from port */
}

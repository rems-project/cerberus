int main() { 
  // on systems where 0xABC is not a legal non-stack/heap 
  // address, does this have undefined behaviour?
  *((int *)0xABC) = 123;
}

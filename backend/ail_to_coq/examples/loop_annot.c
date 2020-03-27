int main() {
  int i;

  [[rc::inv_vars("i : int")]]
  while(1){
    i = i + 1;
  }

  [[rc::inv_vars("i : int")]]
  do {
    i = i + 1;
  } while(1);

  return 0;
}

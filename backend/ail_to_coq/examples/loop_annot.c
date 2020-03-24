int main() {
  int i;

  [[rc::inv("xxx")]]
  while(1){
    i = i + 1;
  }

  [[rc::inv("yyy")]]
  do {
    i = i + 1;
  } while(1);

  return 0;
}

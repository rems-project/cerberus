// returns 0
int main(void) {
  int ret = 0;
  do {
    break;
  } while((ret++, 0));
  return ret;
}

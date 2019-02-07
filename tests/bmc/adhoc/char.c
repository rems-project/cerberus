// UB
int main() {
 char c1 = 0xff;
 unsigned char c2 = 0xff;
 return 1/(c1 == c2);
}

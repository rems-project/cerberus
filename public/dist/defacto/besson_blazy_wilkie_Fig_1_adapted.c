#include <stdio.h>
int set(int p, int flag) { 
  return p | (1 << flag); }
int isset(int p, int flag) { 
  return (p & (1 << flag)) != 0; }
int main() { 
  int status;
  printf("status=0x%x\n",status);
  status = set(status,0); 
  _Bool b = isset(status,0);
  printf("status=0x%x  b=%s\n",status,b?"true":"false");
  return isset(status,0); }

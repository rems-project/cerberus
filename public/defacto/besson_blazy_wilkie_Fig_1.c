int set(int p, int flag) { 
  return p | (1 << flag); }
int isset(int p, int flag) { 
  return (p & (1 << flag)) != 0; }
int main() { 
  int status = set(status,0); 
  return isset(status,0); }

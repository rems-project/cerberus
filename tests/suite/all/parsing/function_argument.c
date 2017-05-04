int a (int b (int c)) {return a(b);}
int b (int c) {return c;}

int main () {return a(b);}

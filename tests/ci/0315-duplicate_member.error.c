struct T2 {
  struct T3 {
    int xx;
    int yy;
  } st1;
  int zz;
  struct T4 {
    int xx;
    int yy;
    int xx; // Error: `xx` is already visible in the current namespace
  } st2;
};

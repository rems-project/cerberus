struct T {
  int x;
  struct T2 {
    int y[2];
    char z;
  } st;
  char c[3];
};

struct T arr1[3] =
  { 1, {{2,3,40,50}, 6,
    "foo"}, [2].st.z= 7};

/*
 * Consider the array object defined by the declaration
 * int x[3][5];
 * Here x is a 3 x 5 array of ints; more precisely, x is an array of three
 * element objects, each of which is an array of five ints. In the expression
 * x[i], which is equivalent to (*((x)+(i))), x is first converted to a pointer
 * to the initial array of five ints. Then i is adjusted according to the type
 * of x, which conceptually entails multiplying i by the size of the object to
 * which the pointer points, namely an array of five int objects. The results
 * are added and indirection is applied to yield an array of five ints. When
 * used in the expression x[i][j], that array is in turn converted to a pointer
 * to the first of the ints, so x[i][j] yields an int.
 */
/* Run with --pp=cabs,ail */
int main()
{
  int x[3][5];
  int i, j;
  x[i];
  x[i][j];
  return 0;
}

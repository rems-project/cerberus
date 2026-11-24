// Companion of 0356-0358: the sequencing that must be preserved around the
// conditional and logical operators. Every line below is defined.
int g;
int get(int a) { return g * 10 + a; } // reads g after the sequence point of the call

int main(void)
{
  int x = 0, r = 0;
  (x = 1) ? x++ : 0;               // sequence point after the first operand: x == 2
  r += x++ ? x : 0;                //                                         x == 3, r == 3
  r += (x++ && x++) + (0 || 0);    // sequence point after the left of &&:    x == 5, r == 4
  r += ((1 ? x++ : 0), x);         // comma after the conditional:            x == 6, r == 10
  int y = 1 ? x++ : 0, z = x;      // full expression of the initializer:     x == 7, y == 6, z == 7
  r += z - y;                      //                                         r == 11
  r += get(1 ? g++ : 0);           // sequence point before the call:         g == 1, r == 21
  if (0 ? 0 : x++) r += x;         // full expression of the condition:       x == 8, r == 29
  x = 1 ? x + 1 : 0;               // no side effect in the operand:          x == 9
  return r + x;                    // returns 38
}

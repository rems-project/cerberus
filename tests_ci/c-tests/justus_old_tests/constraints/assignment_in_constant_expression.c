int global_1 = 0;
int global_2 = sizeof (global_1++);
int global_3 = global_1++;

int main (void) {
  return global_3;
}

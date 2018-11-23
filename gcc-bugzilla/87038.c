#include <stdio.h>
void func(int x) {
        switch (x) {
                case 1: {
                        int foo = 3;
                        case 0:
                                printf("foo is %d\n", foo);
                }
        }
}

int main() {
  func(0);
}

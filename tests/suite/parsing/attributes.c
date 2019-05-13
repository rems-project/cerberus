[[attr1]] struct [[attr2]] ST { int x; } [[attr3]] s1 [[attr4]], s2 [[attr5]];

[[attr1]] int [[attr2]] * [[attr3]] foo([[attr4]] float [[attr5]] f1 [[attr6]],
int i) [[attr7]];

[[attr1]] int [[attr2]] a[10] [[attr3]], b [[attr4]];

struct [[deprecated]] S; // valid, [[deprecated]] appertains to struct S
void f(struct S *s);     // valid, the struct S type has
                         // the [[deprecated]] attribute
struct S {               // valid, struct S inherits the
 int a;                  // [[deprecated]] attribute from
};                       // the previous declaration
void g(struct [[deprecated]] S s); // invalid

struct [[something]] x; /* valid */
void f2(struct [[something]] S); /* invalid */

int main() {
  for ([[attr1]] int i = 0; i < 10; ++i);

  enum e { i [[attr1]] };

   struct S {
     [[attr1]] int i, *j;
     int k [[attr2]];
     int l [[attr3]];
   };
}
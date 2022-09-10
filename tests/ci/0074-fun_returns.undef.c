/* non-void functions must end with a return when their value
  is used, otherwise it is undefined (§6.9.1#12) */
int f() {
  ;
} // potentially undefined

/* this function is fine because its return type is void, the elaboration should place
   a Core "pure(unit)" */
void g() {
  ;
}

// the lack of return allowed is here (§5.1.2.2.3#1 first sentence)
int main(void) {
  g();
  f(); // this call is fine, because unused
  f() + 1; // this one is not
  return f(); // nor is this one
}

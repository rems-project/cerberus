/* the end of non-void functions must not be reached (§6.9.1#12), the
   elaboration should place an undef as the body */
int f() {
  ;
}

/* this function is fine because it return void, the elaboration should place
   a Core "return(unit)" */
void g() {
  ;
}

// the lack of return is here (§5.1.2.2.3#1 first sentence)
int main(void) {
  g(); f();
}

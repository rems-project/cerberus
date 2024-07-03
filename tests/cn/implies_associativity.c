/* Here we test the right associativity of `implies`. Since `implies` is 
   right associative, the expression `false implies true implies false` 
   should be parsed as `false implies (true implies false)`,
   and therefore should always be true. `(false implies true) implies false`
   would fail.
*/

void foo ()
{
    /*@ assert(false implies true implies false); @*/
}
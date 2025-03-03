int foo(int);
/*@ spec foo(i32 x);
requires x < MAXi32();
ensures return == x + 1i32; @*/

/*@ spec foo(i32 y);
requires y < MAXi32() - 1i32;
ensures return == y + 2i32; @*/

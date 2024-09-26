/*
error: CreateReadOnly: not a constant ctype: Ivalignof('char[4]')
	return "abc" == (void *)0;
	       ^~~~~
*/
// Cause: constant string

int
main()
{
	return "abc" != (void *)0;
}

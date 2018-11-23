void g( char *a)
{
  *a = 'x';
}

void f( int n, char * p1)
{
	char * p2;

	p2 = p1;

	if (n >= 0)
	{
		char buf[ 10];

		p2 = buf;
	}
	g( p2);  // Bang !
}

// Not in the error report:
int main()
{
  char c[3];
  f(0, c);
}

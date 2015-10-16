// The occurence of a duplicate typedef with a use of defined type
// (here T) between the two typedefs use to produce a parsing error
// (with location the end of the file)
typedef int T;
void f(T);
typedef int T;

int main(void)
{

}

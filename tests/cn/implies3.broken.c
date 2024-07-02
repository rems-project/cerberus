int foo ()
/*@ requires true implies false;
    ensures false;
@*/
{
    return 0;
}
int main()
{
    int x = 10;

    if (x > 0) {
inner:
        x--;
    }

    if (x > 0) {
        goto inner;
    }

    return x;
}

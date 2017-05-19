// the desugaring should be able to resolve "l2" in the goto...
int main(void)
{
 l1:
 l2:
  goto l2;
}

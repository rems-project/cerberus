
/*@
datatype tree {
  Tree_Empty {},
  Tree_Node {i32 k, i32 v, datatype tree l, datatype tree r}
}

function (i32) foo (datatype tree t) {
  match t {
    Tree_Empty {} => {0i32}
    Tree_Node {k: k, v: v, l: _, r: _} => {k + v}
  }
}
@*/

void
check_foo (int x)
/*@ requires let t = Tree_Node {k: 1i32, v: x, l: Tree_Empty {},
    r: Tree_Node {k: 3i32, v: 0i32, l: Tree_Empty {}, r: Tree_Empty {}}};
    ensures foo(t) == x + 1i32; 
@*/
{
  ;
}

int main(void) {
  check_foo(5);
  return 0;
}

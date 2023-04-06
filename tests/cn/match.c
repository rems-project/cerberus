
datatype tree {
  Tree_Empty {},
  Tree_Node {integer k, integer v, datatype tree l, datatype tree r}
}

function (integer) foo (datatype tree t) {
  return (match t {
    Tree_Empty {} => {0}
    Tree_Node {k: k, v: v} => {k + v}
  });
}


void
check_foo (int x)
/*@ requires let t = Tree_Node {k: 1, v: x, l: Tree_Empty {},
    r: Tree_Node {k: 3, v: 0, l: Tree_Empty {}, r: Tree_Empty {}}} @*/
/*@ ensures foo(t) == x + 1 @*/
{
}



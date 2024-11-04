/* A set defined as binary search tree */

struct MapNode {
    int key;
    int ignore;
    long value;
    struct MapNode* smaller;
    struct MapNode* larger;
};
struct MapNode* malloc_MapNode();
struct Map {
    struct MapNode* root;
};
struct Map map_empty();
_Bool map_lookup(struct Map map, int key, long* value);

// Functional Sepcification of Binary Search Tree
/*@
type_synonym KEY = i32
type_synonym VALUE = i64
type_synonym NodeData = { KEY key, VALUE value }

type_synonym Interval = { KEY lower, KEY upper, boolean empty }

function (Interval) emptyInterval() {
  { lower: 0i32, upper: 0i32, empty: true }
}



function (Interval) joinInterval(Interval smaller, Interval larger) {
  if (smaller.empty) {
    larger
  } else {
  if (larger.empty) {
    smaller
  } else {
    { lower: smaller.lower, upper: larger.upper, empty: false }
  }}
}

// A binary dearch tree
datatype BST {
  Leaf {},
  Node { NodeData data, BST smaller, BST larger }
}

// A selector for the case when we know that the tree is a `Node`.
function ({ NodeData data, BST smaller, BST larger }) fromBSTNode(BST node) {
  match node {
    Leaf {} => { { data: { key: 0i32, value: 0i64 }, smaller: Leaf {}, larger: Leaf {} } }
    Node { data: data, smaller: smaller, larger: larger } => {
      { data: data, smaller: smaller, larger: larger }
    }
  }
}


function [rec] (VALUE) lookup(KEY key, BST tree) {
  match tree {
    Leaf {} => { 0i64 }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (data.key == key) {
        data.value
      } else {
        if (data.key < key) {
          lookup(key,larger)
        } else {
          lookup(key,smaller)
        }
      }
    }
  }
}

function [rec] (boolean) member(KEY k, BST tree) {
  match tree {
    Leaf {} => { false }
    Node { data: data, smaller: smaller, larger: larger } => {
      data.key == k ||
      k < data.key && member(k,smaller) ||
      k > data.key && member(k,larger)
    }
  }
}

function [rec] (BST) insert(KEY key, VALUE value, BST tree) {
  match tree {
    Leaf {} => { Node { data: { key: key, value: value }, smaller: Leaf {}, larger: Leaf {} } }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (data.key == key) {
        Node { data: { key: key, value: value }, smaller: smaller, larger: larger }
      } else {
        if (data.key < key) {
          Node { data: data, smaller: smaller, larger: insert(key,value,larger) }
        } else {
          Node { data: data, smaller: insert(key,value,smaller), larger: larger }
        }
      }
    }
  }
}



function [rec] (BST) setKey(KEY k, BST root, BST value) {
  match root {
    Leaf {} => { value }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (k < data.key) {
        Node { data: data, smaller: setKey(k, smaller, value), larger: larger }
      } else {
        Node { data: data, smaller: smaller, larger: setKey(k, larger, value) }
      }
    }
  }
}


@*/

// Specialized `malloc`
extern struct MapNode* malloc_MapNode();
/*@
spec malloc_MapNode();
requires
  true;
ensures
  take v = Block<struct MapNode>(return);
@*/
/*@

// *****************************************************************************
// Consuming an entire tree
// *****************************************************************************


// Semantic data stored at a node
function (NodeData) getNodeData(struct MapNode node) {
  { key: node.key, value: node.value }
}

type_synonym RangedBST = { BST tree, Interval range }
type_synonym RangedNode = {
  struct MapNode node,
  BST smaller,
  BST larger,
  Interval range
}

function (boolean) validBST(struct MapNode node, Interval smaller, Interval larger) {
  (smaller.empty || smaller.upper < node.key) &&
  (larger.empty || node.key < larger.lower)
}


predicate RangedNode RangedNode(pointer root) {
   take node = Owned<struct MapNode>(root);
   take smaller = RangedBST(node.smaller);
   take larger  = RangedBST(node.larger);
   assert (validBST(node, smaller.range, larger.range));
   return { node: node, smaller: smaller.tree, larger: larger.tree,
            range: joinInterval(smaller.range, larger.range) };
}

// A binary search tree, and the interval for all its keys.
predicate RangedBST RangedBST(pointer root) {
  if (is_null(root)) {
    return { tree: Leaf {}, range: emptyInterval() };
  } else {
    take node = RangedNode(root);
    let data = getNodeData(node.node);
    return { tree: Node { data: data, smaller: node.smaller, larger: node.larger },
             range: node.range };
  }
}

// An arbitrary binary search tree.
predicate BST BST(pointer root) {
  take result = RangedBST(root);
  return result.tree;
}




// *****************************************************************************
// Focusing on a node in the tree
// *****************************************************************************

type_synonym BSTNodeFocus =
  { BST done, struct MapNode node, BST smaller, BST larger }

datatype BSTFocus {
  AtLeaf { BST tree },
  AtNode { BST done, struct MapNode node, BST smaller, BST larger }
}

function (struct MapNode) default_map_node() {
    struct MapNode {
        key: 0i32,
        ignore: 0i32,
        value: 0i64,
        smaller: NULL,
        larger: NULL
    }
}

function (BSTNodeFocus) default_node_focus() {
    { done: Leaf {}, node: default_map_node(), smaller: Leaf {}, larger: Leaf {} }
}

// Access focus data, when we already know that we are at a node.
function (BSTNodeFocus) fromBSTFocusNode(BSTFocus focus) {
  match focus {
    AtLeaf { tree: _ } => { default_node_focus() }
    AtNode { done: done, node: node, smaller: smaller, larger: larger } => {
      { done: done, node: node, smaller: smaller, larger: larger }
    }
  }
}

predicate BSTFocus BSTFocus(pointer root, pointer child) {
  if (is_null(child)) {
    take tree = BST(root);
    return AtLeaf { tree: tree };
  } else {
    take node    = RangedNode(child);
    take result  = BSTNodeUpTo(root, child, node.node, node.range);
    return AtNode { done: result.tree, node: node.node,
                    smaller: node.smaller, larger: node.larger };
  }
}

// Consume parts of the tree starting at `p` until we get to `c`.
// We do not consume `c`.
// `child` is the node stored at `c`.
predicate RangedBST BSTNodeUpTo(pointer p, pointer c, struct MapNode child, Interval range) {
  if (ptr_eq(p,c)) {
    return { tree: Leaf {}, range: range };
  } else {
    take parent = Owned<struct MapNode>(p);
    take result = BSTNodeChildUpTo(c, child, range, parent);
    return result;
  }
}

// Starting at a parent with data `data` and children `smaller` and `larger`,
// we go toward `c`, guided by its value, `target`.
predicate RangedBST
  BSTNodeChildUpTo(pointer c, struct MapNode target, Interval range, struct MapNode parent) {
  if (parent.key < target.key) {
    take small = RangedBST(parent.smaller);
    take large = BSTNodeUpTo(parent.larger, c, target, range);
    assert(validBST(parent, small.range, large.range));
    return { tree: Node { data: getNodeData(parent), smaller: small.tree, larger: large.tree },
             range: joinInterval(small.range,large.range) };
  } else {
  if (parent.key > target.key) {
    take small = BSTNodeUpTo(parent.smaller, c, target, range);
    take large = RangedBST(parent.larger);
    assert(validBST(parent, small.range, large.range));
    return { tree: Node { data: getNodeData(parent), smaller: small.tree, larger: large.tree },
             range: joinInterval(small.range,large.range) };
  } else {
    // We should never get here, but asserting `false` is not allowed
    return { tree: Leaf {}, range: emptyInterval() };
  }}
}

function (BST) unfocus(BSTFocus focus) {
  match focus {
    AtLeaf { tree: tree } => { tree }
    AtNode { done: tree, node: node, smaller: smaller, larger: larger } => {
      let bst = Node { data: getNodeData(node), smaller: smaller, larger: larger };
      setKey(node.key, tree, bst)
    }
  }
}

function (BST) focusDone(BSTFocus focus) {
  match focus {
    AtLeaf { tree: tree } => { tree }
    AtNode { done: tree, node: _, smaller: _, larger: _ } => { tree }
  }
}



lemma FocusedGo(pointer root, pointer cur, boolean smaller)
  requires
    !is_null(cur);
    take focus = BSTFocus(root,cur);
  ensures
    let node = fromBSTFocusNode(focus).node;
    take new_focus = BSTFocus(root, if (smaller) { node.smaller } else { node.larger });
    unfocus(focus) == unfocus(new_focus);


// It's quite unfortunate that we have to copy the lemma here.
lemma FocusedGoKey(pointer root, pointer cur, boolean smaller, KEY key)
  requires
    !is_null(cur);
    take focus = BSTFocus(root,cur);
  ensures
    let node = fromBSTFocusNode(focus).node;
    take new_focus = BSTFocus(root, if (smaller) { node.smaller } else { node.larger });
    unfocus(focus) == unfocus(new_focus);

    if (!member(key, focusDone(focus)) && node.key != key) {
      !member(key, focusDone(new_focus))
    } else {
      true
    };



@*/
/* Look for a node and its parent */
struct MapNode* findNode(struct MapNode* root, int key)
    /*@
    requires
      take tree = BST(root);
    ensures
      take focus = BSTFocus(root, return);
      unfocus(focus) == tree;
      match focus {
        AtLeaf { tree: _ } => { !member(key,tree) }
        AtNode { done: _, node: node, smaller: _, larger: _ } => {
          node.key == key
        }
      };
    @*/
{
    struct MapNode* cur = root;
    /*@ split_case is_null(cur); @*/
    /*@ unfold setKey(fromBSTNode(tree).data.key, Leaf {}, tree); @*/
    /*@ unfold member(key, Leaf {}); @*/
    while (cur)
        /*@ inv
        {root} unchanged;
        {key} unchanged;
        take focus = BSTFocus(root,cur);
        unfocus(focus) == tree;
        !member(key, focusDone(focus));
        let cur_prev = cur;
        @*/
    {
        int k = cur->key;
        if (k == key) return cur;
        cur = k < key ? cur->larger : cur->smaller;
        /*@ apply FocusedGoKey(root, cur_prev, k > key, key); @*/
    }
    return 0;
}
/*@
predicate BSTFocus FindParentFocus(pointer tree_ptr,  pointer cur_ptr, pointer parent_ptr, KEY key) {
  if (is_null(cur_ptr)) {
    take focus = BSTFocus(tree_ptr, parent_ptr);
    let tree_after = unfocus(focus);
    assert(!member(key,tree_after)); // More?
    return focus;
  } else {
    // Found in tree
    take focus = BSTFocus(tree_ptr, cur_ptr);
    let at_node = fromBSTFocusNode(focus);
    assert(at_node.node.key == key);
    return focus;
  }
}
@*/
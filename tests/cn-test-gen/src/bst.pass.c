#include <stddef.h>

#define KEY    int
#define VALUE  long

struct MapNode {
  KEY key;
  VALUE value; 
  struct MapNode *smaller;
  struct MapNode *larger;
};

extern void* cn_malloc(size_t size);
extern void cn_free_sized(void *ptr, size_t size);


/*@

type_synonym KEY = i32
type_synonym VALUE = i64
type_synonym NodeData = { KEY key, VALUE value }

function (KEY) defaultKey() { 0i32 }
function (VALUE) defaultValue() { 0i64 }
function (NodeData) defaultNodeData() { 
  { key: defaultKey(), value: defaultValue() }
}

datatype ValueOption {
  ValueNone {},
  ValueSome { VALUE value }
}


// -----------------------------------------------------------------------------
// Intervals

// Non-empty, closed intervals
type_synonym Interval = { KEY lower, KEY upper }

function (Interval) defaultInterval() {
  { lower: defaultKey(), upper: defaultKey() }
}

datatype IntervalOption {
  IntervalNone {},
  IntervalSome { Interval i }
}

function (boolean) isIntervalSome(IntervalOption i) {
  match i {
    IntervalNone {} => { false }
    IntervalSome { i:_ } => { true }
  }
}

function (Interval) fromIntervalOption(IntervalOption i) {
  match i {
    IntervalNone {}      => { defaultInterval() }
    IntervalSome { i:j } => { j }
  }
}


function (IntervalOption)
  joinInterval(IntervalOption optSmaller, KEY val, IntervalOption optLarger) {
  match optSmaller {
    IntervalNone {} => {
      match optLarger {
        IntervalNone {} => {
          IntervalSome { i: { lower: val, upper: val } }
        }
        IntervalSome { i: larger } => {
          if (val < larger.lower) {
            IntervalSome { i: { lower: val, upper: larger.upper } }
          } else {
            IntervalNone {}
          }
        }
      }
    }
    IntervalSome { i: smaller } => {
      if (val > smaller.upper) { 
        match optLarger {
          IntervalNone {} => {
            IntervalSome { i: { lower: smaller.lower, upper: val } }
          }
          IntervalSome { i: larger } => {
            if (val < larger.lower) {
              IntervalSome { i: { lower: smaller.lower, upper: larger.upper } }
            } else {
              IntervalNone {}
            }
          }
        }
      } else {
        IntervalNone {}
      }
    }
  }
}



// -----------------------------------------------------------------------------




// A binary dearch tree
datatype BST {
  Leaf {},
  Node { NodeData data, BST smaller, BST larger }
}

function (boolean) hasRoot(KEY key, BST tree) {
  match tree {
    Leaf {} => { false }
    Node { data: data, smaller: _, larger: _ } => { data.key == key }
  }
}

function (boolean) isLeaf(BST tree) {
  match tree {
    Leaf {} => { true }
    Node { data: _, smaller: _, larger: _ } => { false }
  }
}

function [rec] (ValueOption) lookup(KEY key, BST tree) {
  match tree {
    Leaf {} => { ValueNone {} }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (data.key == key) {
        ValueSome { value: data.value }
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
    Leaf {} => { Node { data: { key: key, value: value },
                        smaller: Leaf {}, larger: Leaf {} } }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (data.key == key) {
        Node { data: { key: key, value: value },
               smaller: smaller, larger: larger }
      } else {
        if (data.key < key) {
          Node { data: data,
                 smaller: smaller, larger: insert(key,value,larger) }
        } else {
          Node { data: data,
                 smaller: insert(key,value,smaller), larger: larger }
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




// *****************************************************************************
// Consuming an entire tree
// *****************************************************************************


// Semantic data stored at a node
function (NodeData) getNodeData(struct MapNode node) {
  { key: node.key, value: node.value }
}

type_synonym RangedBST = { BST tree, IntervalOption range }
type_synonym RangedNode = {
  struct MapNode node,
  BST smaller,
  BST larger,
  Interval range
}

predicate RangedNode RangedNode(pointer root) {
   take node = Owned<struct MapNode>(root);
   take smaller = RangedBST(node.smaller);
   take larger  = RangedBST(node.larger);
   let rangeOpt = joinInterval(smaller.range, node.key, larger.range);
   assert (isIntervalSome(rangeOpt));
   return { node: node, smaller: smaller.tree, larger: larger.tree,
            range: fromIntervalOption(rangeOpt) };
}

// A binary search tree, and the interval for all its keys.
predicate RangedBST RangedBST(pointer root) {
  if (is_null(root)) {
    return { tree: Leaf {}, range: IntervalNone{} };
  } else {
    take node = RangedNode(root);
    let data = getNodeData(node.node);
    return { tree: Node { data: data, smaller: node.smaller, larger: node.larger },
             range: IntervalSome { i: node.range } };
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
    return { tree: Leaf {}, range: IntervalSome { i: range } };
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
    let node = getNodeData(parent);
    let optRange = joinInterval(small.range, node.key, large.range);
    assert(isIntervalSome(optRange));
    return { tree: Node { data: node, smaller: small.tree, larger: large.tree },
             range: optRange };
  } else {
  if (parent.key > target.key) {
    take small = BSTNodeUpTo(parent.smaller, c, target, range);
    take large = RangedBST(parent.larger);
    let node = getNodeData(parent);
    let optRange = joinInterval(small.range, node.key, large.range);
    assert(isIntervalSome(optRange));
    return { tree: Node { data: node, smaller: small.tree, larger: large.tree },
             range: optRange };
  } else {
    // We should never get here, but asserting `false` is not allowed
    return { tree: Leaf {}, range: IntervalNone {} };
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



@*/


/* Allocate a new singleton node */
struct MapNode *newNode(KEY key, VALUE value)
/*@
requires
  true;
ensures
  take node = Owned<struct MapNode>(return);
  node.key == key;
  node.value == value;
  is_null(node.smaller);
  is_null(node.larger);
@*/
{
  struct MapNode *node = (struct MapNode*)cn_malloc(sizeof(struct MapNode));
  node->key = key;
  node->value = value;
  node->smaller = 0;
  node->larger = 0;
  return node;
}


struct MapNode *findParent(struct MapNode **node, KEY key)
/*@
requires
  take tree_ptr = Owned<struct MapNode*>(node);
  take tree     = BST(tree_ptr);
ensures
  take cur_ptr  = Owned<struct MapNode*>(node);
  let not_found = is_null(cur_ptr);
  not_found == !member(key, tree);
  take focus = BSTFocus(tree_ptr, return);
  unfocus(focus) == tree;
  match focus {
    AtLeaf { tree: _ } => {
      not_found || ptr_eq(cur_ptr,tree_ptr) && hasRoot(key, tree)
    }
    AtNode { done: _, node: parent, smaller: _, larger: _ } => {
      let tgt = if (key < parent.key) { parent.smaller } else { parent.larger };
      ptr_eq(cur_ptr,tgt)    
    }
  };
@*/
{
  struct MapNode *parent = 0;
  struct MapNode *cur = *node;
  while (cur)
  {
    KEY k = cur->key;
    if (k == key) {
      *node = cur;
      return parent;
    }
    parent = cur;
    cur = k < key? cur->larger : cur->smaller;
  }
  *node = cur;
  return parent;
}

/* Insert an element into a map. Overwrites previous if already present. */
void map_insert(struct MapNode **root, KEY key, VALUE value)
/*@
requires
  take root_ptr = Owned(root);
  take tree = BST(root_ptr);
ensures
  take new_root = Owned(root);
  take new_tree = BST(new_root);
  new_tree == insert(key, value, tree);
@*/
{
  struct MapNode *search = *root;
  struct MapNode *parent = findParent(&search, key);
  if (search) {
    search->value = value;
    return;
  }

  if (!parent) {
    *root = newNode(key,value);
    return;
  }

  struct MapNode *new_node = newNode(key,value);
  if (parent->key < key) {
    parent->larger = new_node;
  } else {
    parent->smaller = new_node;
  }
}

/*@
function [rec] ({ boolean empty, NodeData data, BST tree }) delLeast(BST root) {
  match root {
    Leaf {} => { { empty: true, data: defaultNodeData(), tree: Leaf {} } }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (isLeaf(smaller)) {
        { empty: false, data: data, tree: larger }
      } else {
         let res = delLeast(smaller);
         { empty: false,
           data: res.data,
           tree: Node { data: data, smaller: res.tree, larger: larger }
         }
      }
    }
  }
}

predicate (void) DeleteSmallest(pointer cur, NodeData data) {
  if (is_null(cur)) {
    assert(data == defaultNodeData());
    return;
  } else {
    take node = Owned<struct MapNode>(cur);
    assert(node.key == data.key);
    assert(node.value == data.value);
    return;
  }
}
@*/

struct MapNode* deleteSmallest(struct MapNode **root)
/*@
  requires
    take root_ptr = Owned(root);
    take tree = BST(root_ptr);
  ensures
    take new_root = Owned(root);
    take new_tree = BST(new_root);
    let res = delLeast(tree);
    new_tree == res.tree;
    take unused = DeleteSmallest(return, res.data);
@*/
{
  struct MapNode *cur = *root;
  if (!cur) return 0;

  struct MapNode *parent = 0;
  while (cur->smaller) {
    parent = cur;
    cur = cur->smaller;
  }

  if (parent) {
    parent->smaller = cur->larger;
  }
  //! //
  else {
    *root = cur->larger;
  }
  //!! forget_to_update_root //
  //! //

  return cur;
}

/*@
function [rec] (BST) delKey(KEY key, BST root) {
  match root {
    Leaf {} => { Leaf {} }
    Node { data: data, smaller: smaller, larger: larger } => {
      if (key == data.key) {
        let res = delLeast(larger);
        if (res.empty) {
          smaller
        } else {
          Node { data: res.data, smaller: smaller, larger: res.tree }
        }
      } else {
        //! //
        if (key < data.key) {
          Node { data: data, smaller: delKey(key, smaller), larger: larger }
        } else {
          Node { data: data, smaller: smaller, larger: delKey(key, larger) }
        }
        //!! delete_4_spec //
        //! if (key < data.key) { delKey(key, smaller) } else { delKey(key, larger) } //
        //!! delete_5_spec //
        //! if (key > data.key) { Node { data: data, smaller: delKey(key, smaller), larger: larger } } else { Node { data: data, smaller: smaller, larger: delKey(key, larger) } } //
      }
    }
  }
}
@*/

void deleteKey(struct MapNode **root, KEY key)
/*@
requires
  take root_ptr = Owned(root);
  take tree = BST(root_ptr);
ensures
  take new_ptr = Owned(root);
  take new_tree = BST(new_ptr);
  delKey(key, tree) == new_tree;
@*/
{
  struct MapNode *found = *root;
  struct MapNode *parent = findParent(&found, key);

  if (!found) { return; }
  struct MapNode *remove = deleteSmallest(&found->larger);
  if (remove) {
    found->key = remove->key;
    found->value = remove->value;
  } else {
    remove = found;
    //! //
    if (!parent) {
    //!! always_update_root_instead_of_parent //
    //! if (1) { //
      *root = found->smaller;
    //! //
    } else if (key < parent->key) {
    //!! always_assign_smaller //
    //! } else if (1) { //
      parent->smaller = found->smaller;
    } else if (key > parent->key) {
      parent->larger = found->smaller;
    } else {
      /* unreachable */
    }
  }
  cn_free_sized(remove, sizeof(struct MapNode));
}

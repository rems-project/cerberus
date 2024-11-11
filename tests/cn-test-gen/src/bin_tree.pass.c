void* cn_malloc(unsigned long size);

struct int_tree {
    int key;
    struct int_tree* left;
    struct int_tree* right;
};

/*@
    datatype binary_tree {
        Tree_Leaf {},
        Tree_Node { i32 key, datatype binary_tree left, datatype binary_tree right }
    }
    predicate (datatype binary_tree) IntTree(pointer p) {
        if (is_null(p)) {
            return Tree_Leaf {};
        } else {
            take n = Owned<struct int_tree>(p);
            take l = IntTree(n.left);
            take r = IntTree(n.right);
            return Tree_Node { key: n.key, left: l, right: r };
        }
    }
@*/

struct int_tree* deepCopyRecursive(struct int_tree* p)
    /*@
        requires
            take T = IntTree(p);
        ensures
            take T_ = IntTree(p);
            T == T_;
            take T2 = IntTree(return);
            T == T2;
    @*/
{
    if (p == 0) {
        return 0;
    }
    struct int_tree* q = cn_malloc(sizeof(struct int_tree));
    q->key = p->key;
    q->left = deepCopyRecursive(p->left);
    q->right = deepCopyRecursive(p->right);
    return q;
}

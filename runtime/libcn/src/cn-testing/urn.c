#include <assert.h>
#include <stdlib.h>

#include <cn-testing/uniform.h>
#include <cn-testing/urn.h>

int is_leaf(struct cn_gen_int_tree* tree) {
  return tree->left == NULL && tree->right == NULL;
}

uint64_t sample_tree_det(struct cn_gen_int_tree* tree, uint64_t index) {
  if (tree == NULL) {
    return -1;
  }

  if (is_leaf(tree)) {
    return tree->value;
  }

  if (index < tree->left->weight) {
    return sample_tree_det(tree->left, index);
  }

  return sample_tree_det(tree->right, index - tree->left->weight);
}

uint64_t sample_urn(struct cn_gen_int_urn* urn) {
  uint64_t index =
      convert_from_cn_bits_u64(cn_gen_uniform_cn_bits_u64(urn->tree->weight));
  return sample_tree_det(urn->tree, index);
}

struct cn_gen_int_tree* insert_tree(
    uint8_t path, struct cn_gen_int_tree* tree, struct cn_gen_int_tree* leaf) {
  if (tree == NULL) {
    return leaf;
  }

  if (is_leaf(tree)) {
    struct cn_gen_int_tree* res =
        (struct cn_gen_int_tree*)malloc(sizeof(struct cn_gen_int_tree));
    res->weight = tree->weight + leaf->weight;
    res->left = tree;
    res->right = leaf;
    return res;
  }

  if (path & 1) {
    tree->weight += leaf->weight;
    tree->right = insert_tree(path >> 1, tree->right, leaf);
  } else {
    tree->weight += leaf->weight;
    tree->left = insert_tree(path >> 1, tree->left, leaf);
  }
  return tree;
}

void urn_insert(struct cn_gen_int_urn* urn, uint64_t weight, uint64_t value) {
  struct cn_gen_int_tree* leaf =
      (struct cn_gen_int_tree*)malloc(sizeof(struct cn_gen_int_tree));
  leaf->weight = weight;
  leaf->value = value;
  leaf->left = NULL;
  leaf->right = NULL;

  urn->tree = insert_tree(urn->size, urn->tree, leaf);
  urn->size += 1;
}

struct cn_gen_int_urn* urn_from_array(uint64_t elems[], uint8_t len) {
  struct cn_gen_int_urn* urn =
      (struct cn_gen_int_urn*)malloc(sizeof(struct cn_gen_int_urn));
  urn->size = 0;
  urn->tree = NULL;
  for (uint16_t i = 0; i < 2 * (uint16_t)len; i += 2) {
    if (elems[i] != 0) {
      urn_insert(urn, elems[i], elems[i + 1]);
    }
  }
  return urn;
}

struct replace_res {
  uint64_t weightOld;
  uint64_t valueOld;

  uint64_t weightNew;
  uint64_t valueNew;
};

struct replace_res replace_tree(
    struct cn_gen_int_tree* tree, uint64_t weight, uint64_t value, uint64_t index) {
  if (tree == NULL) {
    assert(false);
  }

  if (is_leaf(tree)) {
    struct replace_res res = (struct replace_res){.weightOld = tree->weight,
        .valueOld = tree->value,

        .weightNew = weight,
        .valueNew = value};

    tree->weight = weight;
    tree->value = value;

    return res;
  }

  if (index < tree->left->weight) {
    struct replace_res res = replace_tree(tree->left, weight, value, index);

    tree->weight = tree->weight - res.weightOld + res.weightNew;

    return res;
  } else {
    struct replace_res res =
        replace_tree(tree->right, weight, value, (index - tree->left->weight));

    tree->weight = tree->weight - res.weightOld + res.weightNew;

    return res;
  }
}

uint64_t replace(
    struct cn_gen_int_urn* urn, uint64_t weight, uint64_t value, uint64_t index) {
  return replace_tree(urn->tree, weight, value, index).valueOld;
}

struct uninsert_res {
  uint64_t weight;
  uint64_t value;

  uint64_t lowerBound;

  struct cn_gen_int_tree* tree;
};

struct uninsert_res uninsert_tree(uint8_t path, struct cn_gen_int_tree* tree) {
  if (tree == NULL) {
    assert(false);
  }

  if (is_leaf(tree)) {
    uint64_t weight = tree->weight;
    uint64_t value = tree->value;
    free(tree);
    return (struct uninsert_res){.weight = weight, .value = value, .tree = NULL};
  }

  if (path & 1) {
    struct uninsert_res res = uninsert_tree(path >> 1, tree->right);
    tree->right = res.tree;
    tree->weight -= res.weight;

    res.tree = tree;
    res.lowerBound += tree->left->weight;
    return res;
  } else {
    struct uninsert_res res = uninsert_tree(path >> 1, tree->left);
    tree->left = res.tree;
    tree->weight -= res.weight;

    res.tree = tree;
    return res;
  }
}

struct uninsert_res uninsert_urn(struct cn_gen_int_urn* urn) {
  urn->size -= 1;
  return uninsert_tree(urn->size, urn->tree);
}

uint64_t remove_urn_det(struct cn_gen_int_urn* urn, uint64_t index) {
  struct uninsert_res res = uninsert_urn(urn);

  if (res.tree == NULL) {
    return res.value;
  }

  if (index < res.lowerBound) {
    return replace(urn, res.weight, res.value, index);
  } else if (index < res.lowerBound + res.weight) {
    return res.value;
  } else {
    return replace(urn, res.weight, res.value, index - res.weight);
  }
}

uint64_t urn_remove(struct cn_gen_int_urn* urn) {
  uint64_t index =
      convert_from_cn_bits_u64(cn_gen_uniform_cn_bits_u64(urn->tree->weight));
  return remove_urn_det(urn, index);
}

void tree_free(struct cn_gen_int_tree* tree) {
  if (tree == NULL) {
    return;
  }

  if (is_leaf(tree)) {
    return free(tree);
  }

  tree_free(tree->left);
  tree_free(tree->right);
  return free(tree);
}

void urn_free(struct cn_gen_int_urn* urn) {
  free(urn->tree);
  free(urn);
}

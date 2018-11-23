struct array {
    int data[3];
};

void foo2(struct array* value, const struct array* value2) {
    if (&value == &value2) return;
    value->data[0] = value2->data[0];
    value->data[1] = value2->data[0];
    value->data[2] = value2->data[0];
}

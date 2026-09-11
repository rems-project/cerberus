int* id_escape(int y) {
    int x = y;
    return &x;
}

int main() {
    id_escape(0);
    return 0;
}

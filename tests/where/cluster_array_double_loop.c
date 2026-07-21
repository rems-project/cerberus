typedef struct cluster_t {
    int size; // Number in cluster
    signed char* chars; // Array in cluster
} cluster_t;

int tester(cluster_t* clusters)
{
    int total = 0;
    for (int k=0; k<10; k++)
    {
        cluster_t *cluster_k = &clusters[k];
        for (int i = 0; i < cluster_k->size; i++)
        {
            if (cluster_k->chars[i] < 0) return -1;
            total += cluster_k->chars[i];
        }
    }

    if (total > 100) total -= 10;
    return total;
}

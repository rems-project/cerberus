#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static size_t size = 0;
static size_t capacity = 0;
static char** lines = NULL;

void cn_replica_lines_append(char* line) {
  if (size == capacity) {
    capacity = (capacity == 0) ? 8 : 2 * capacity;
    lines = realloc(lines, capacity * sizeof(char*));
    if (lines == NULL) {
      fprintf(stderr, "Failed to expand reproduction array\n");
      abort();
    }
  }

  lines[size++] = line;
}

void cn_replica_lines_reset() {
  for (int i = 0; i < size; i++) {
    // free(lines[i]); // TODO: free lines
  }
  free(lines);
  lines = NULL;

  size = 0;
  capacity = 0;
}

char* cn_replica_lines_to_str() {
  size_t sz = 0;
  for (int i = 0; i < size; i++) {
    sz += strlen(lines[i]) + 1;  // +1 for newline
  }

  char* res = malloc(sz + 1);
  for (int i = 0; i < size; i++) {
    strcat(res, lines[i]);
    strcat(res, "\n");
  }

  return res;
}

#ifndef CN_LINES_H
#define CN_LINES_H

#ifdef __cplusplus
extern "C" {
#endif

void cn_replica_lines_append(char* line);
void cn_replica_lines_reset();
char* cn_replica_lines_to_str();

#ifdef __cplusplus
}
#endif

#endif /* CN_LINES_H */

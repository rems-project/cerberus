#include <dirent.h>
#include <string.h>

int main () {
  const char* name = "fs";
  DIR *dirp = opendir(".");
  if (dirp == NULL)
    return 1;
  int len = strlen(name);
  struct dirent *dp;
  while ((dp = readdir(dirp)) != NULL) {
    if (dp->d_namlen == len && strcmp(dp->d_name, name) == 0) {
      closedir(dirp);
      return 0;
    }
  }
  closedir(dirp);
  return 1;
}

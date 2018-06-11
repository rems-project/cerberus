#include "cerberus.h"
/* Make sure that we don't free any temp stack slots associated with
   initializing marker before we're finished with them.  */


typedef struct { short v16; }  jint16_t;

struct node {
  jint16_t magic;
  jint16_t nodetype;
  int totlen;
} ;

struct node node, *node_p = &node;

int 
main (void)
{
  struct node marker = {
    .magic = (jint16_t) {0x1985},
    .nodetype = (jint16_t) {0x2003},
    .totlen = node_p->totlen
  };
  if (marker.magic.v16 != 0x1985)
    abort();
  if (marker.nodetype.v16 != 0x2003)
    abort();
  return 0;
}

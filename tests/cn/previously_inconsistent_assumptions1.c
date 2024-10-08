/* https://github.com/rems-project/cerberus/issues/566 */

struct in_addr {
    int s_addr;  // load with inet_aton()
};
 
 
extern int test(struct in_addr* addr);
/*@
  spec test(pointer addr);
  requires take x =Owned<struct in_addr>(addr);
  ensures take x2 =Owned<struct in_addr>(addr);
@*/

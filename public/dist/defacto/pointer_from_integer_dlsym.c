dynamic linker
...on loading a new object, decides the base load address and reserves that virtual address space, using mmap.  Note that there may not be any memory at the start of that address.


plugin.so
...get base address of loaded object, as an Elf64_Addr - an integer type of the size of pointer in the ABI, eg uint64_t
...get integer array index into dynamic symbol table of loaded object
...get value of symbol: byte offset from base address of loaded object
...add the base address and offset together
...cast to void* and return


// client
void *handle = dlopen("/path/to/plugin.so",RTLD_NOW);
void *plugin_global_1 = dlsym(handle, "plugin_global_1");
void *plugin_global_2 = dlsym(handle, "plugin_global_2");
int *g1 = plugin_global_1;
int *g2 = plugin_global_1;

... does alias analysis assume g1 <> g2 ?  It shouldn't, because distinct symbols can point to the same address.'



-------------

  


  
  

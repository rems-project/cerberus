# fix lem bugs
s/let |||> /let (|||>) /
s/let ||| /let (|||) /
s/with sexp_of/[@@deriving sexp]/g
s/with sexp/[@@deriving sexp]/g
s/>>=/(>>=)/g
s/|||/(|||)/g
s/<(|||)>/(<|||>)/g
s/Fs_types\.//g
s/Fs_arch\.//g
s/Fs_permissions\.//g
s/Resolve\.//g
s/Fs_operations\.//g
s/Fs_transition_system\.//g
s/Os_operations\.//g
s/Os_transition_system\.//g
s/The_monad\.//g

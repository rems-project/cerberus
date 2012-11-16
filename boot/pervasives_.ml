exception BUG   of string
exception ERROR of string

let raise_bug msg = raise (BUG msg)
let raise_error msg = raise (ERROR msg)

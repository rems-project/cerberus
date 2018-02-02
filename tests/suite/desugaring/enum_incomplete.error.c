// the inner occurence of enum T is invalid, because this
// type is incomplete until the closing }
enum T { A= sizeof(enum T) };

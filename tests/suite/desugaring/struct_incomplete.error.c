// the inner occurence of struct T is invalid, because this
// type is incomplete until the closing }
struct T {
  struct T st;
};

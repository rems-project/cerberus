// the inner occurence of union T is invalid, because this
// type is incomplete until the closing }
union T {
  union T un;
};

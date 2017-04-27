#include <stdio.h>

int main(void)
{
  int x[2] = {10,20}, *p = x;
  printf("*p++ ==> %d\n", *p++); // EXPECTING: "*p++ ==> 10\n"
  printf("*p   ==> %d\n", *p);   // EXPECTING: "*p   ==> 20\n"
}


/*

EDecl_func[Fundec[{[], [TSpec_int], [], [], []},


Declarator[None, DDecl_function[DDecl_identifier[main], [Params[PDeclaration_abs_decl[{[], [TSpec_void], [], [], []}, None], false]]]],


CabsSblock[

[CabsSdecl[

Declaration_base[{[], [TSpec_int], [], [], []}, [InitDecl[Declarator[Some(PDecl[[], None]), DDecl_identifier[p]], Some (Init_expr[CabsEident[x]])], InitDecl[Declarator[None, DDecl_array[DDecl_identifier[x], ADecl[[], false,Some(ADEclSize_expression[CabsEconst[2]])]]], Some (Init_list[Init_expr[CabsEconst[10]], Init_expr[CabsEconst[20]]])]]]

]]


]



]]

*/

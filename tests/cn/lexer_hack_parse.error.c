// This test used to give a bad parsing error because of the lexer feedback
// hack mutability: https://github.com/rems-project/cerberus/issues/382

/*@
@*/

/*@

datatype DT { Cons {} }

function [rec] (datatype DT) split(datatype DT xs) {
    match xs {
        Cons {} =>
            Cons {}
    }
}

@*/

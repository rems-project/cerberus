Classification of the files in model/
======

## Utility modules (including Monads)
* bimap.lem
* boot.lem
* debug.lem
* dlist.lem
* enum.lem
* errors.lem
* exception.lem
* exception_undefined.lem
* float.lem
* global.lem
* loc.lem
* monadic_parsing.lem
* multiset.lem
* nondeterminism.lem
* nondeterminism2.lem
* pp.lem                                  Lem wrapper for pretty printing
* product.lem
* scope_table.lem
* state.lem
* state_exception.lem
* state_exception_undefined.lem
* std.lem
* symbol.lem
* symbolic.lem
* uniqueId.lem
* utils.lem


## Concurrency stuff (better to ignore)
* cmm_aux.lem
* cthread.lem


## Modules which are morally dead but still needed to compile
* constraints.lem
    broken constraint types (from before Z3)

* implementation_.lem
    module pretending to list implementation-defined things. This is mostly dead.


FROM HERE THE INTERESTING MODULES:
======

The modules part of the pipeline are (in order) :

   Cabs_to_ail         the desugaring from Cabs to Ail (untyped)
   ail/GenTyping       the typing and annotating of Ail
   Translation         the elaboration of Ail (typed) in Core
   Core_typing         the typing of Core
   Driver              the runtime of Core (using Core_run and Core_eval)
                       and a memory model (Defacto_memory2)

the actual implementation of the pipeline is written in OCaml (see src/main.ml)

to see a condensed implentation of the pipeline in Lem, see the WipFrontend
module

The modules defining the source/intermediate languages are:

   Cabs                  the C abstract syntax
   ail/AilSyntax         
   ail/AilTypes          a slighy more principled version of C (which
                         symbols for names)
   Core                  the target Core language



MORE DETAILS ABOUT THE INTERESTING MODULES:
=====

* builtins.lem
     contains maps from Cabs builtin identifiers and types (e.g. INT_MAX) to
     the corresponding Ail constructs. This is used by the desugaring.


* cabs.lem
     definitions for the Cabs language


* core.lem
* core_aux.lem
     definitions and auxiliary functions for the Core language

* core_ctype.lem
* core_ctype_aux.lem 
     definitions and auxiliary functions for the C types used by Core


* cabs_to_ail.lem
* cabs_to_ail_aux.lem
* cabs_to_ail_effect.lem
     desugaring from Cabs to Ail (untyped)


* core_eval.lem
     Big-step semantics for the Core pure expressions


* core_indet.lem
     Core to Core rewriting functions to solve C's "indeterminate sequencing"
     (currently the code actually doing the work is commented out)


* core_rewrite.lem
     some Core to Core rewriting functions. These rewrites are technically not
     necessary, but they help make the generated Core more readable and reduce
     nondeterminism (the Core runtime is a bit trigger happy).


* core_run.lem
* core_run_aux.lem
* core_run_effect.lem
     Small-step semantics for the Core expressions. This also calls the Core_eval
     module for the pure part of the dynamics.


* core_sequentialise.lem
     Core to core rewriting getting rid of the Eunseq construct. This is used
     by the Core to OCaml backend.


* core_typing.lem
* core_typing_aux.lem
* core_typing_effect.lem
     typechecker for Core


* driver.lem
     this module drives the Core dynamics using the steps provided by Core_run.
     It does the linking with the memory model (though Mem.lem) and in the days
     when the concurrency worked it did the linking with Kyndylan's stuff.


* decode.lem
     fake module (it uses OCaml functions) to map C integer/character constants
     into semantics values. This module makes a choice regarding the
     implementation details.


* defacto_memory2.lem
* defacto_memory_aux2.lem
* defacto_memory_types2.lem
     the currently "working" implementation of the Core memory model API as
     exposed by Mem.lem


* mem.lem
* mem_aux.lem
* mem_common.lem
     The Core memory model API. This module only defines the API and
     currently forwards Defacto_memory2. We do things this way because we
     don't have functors in Lem.


* output.lem
     implementation of printf()


* translation.lem
* translation_aux.lem
* translation_effect.lem
     The Ail (typed) to Core elaboration module. This is the central
     part of cerberus.


* undefined.lem
     this module defines C's undefined behaviours.


* wipFrontend.lem
     this module is a small condensed version of the whole pipeline (written
     in the Lem unlike the actual pipeline which is in src/main.ml). This
     is used during Desugaring (Cabs_to_ail.lem) when the value of some
     integer constants need to be known.


* ail/AilSyntax.lem
* ail/AilSyntaxAux.lem
     definitions for the syntax of the Ail language

* ail/AilTypes.lem
* ail/AilTypesAux.lem
     definitions for the types of the Ail language

* ail/AilTyping.lem
     utility functions for the typechecking of Ail

* ail/AilWf.lem
     some well-formedness predicates for the Ail and Ail types

* ail/GenTypes.lem
* ail/GenTypesAux.lem
     a slightly more abstract version of Ail (only) used by the
     Ail typechecker.

* ail/GenTyping.lem
     were the Ail typechecking (and annotation) actually happens.

* Common.lem
* Context.lem
* ErrorMonad.lem
* Implementation.lem
* Range.lem
* TypingError.lem
     utility modules used the Ail typechecking
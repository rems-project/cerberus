# Things to do

## Small pending tasks

   - More polishing on pp.mli

## Information that would be useful to add, generally

Some useful high-level information we could add (e.g. to this file :-)...

   - Where is the parser?  How does it connect to the rest?
   - What is the relation between the Cerberus and CN codebases?
   - What are the main starting points in this directory?
   - If I want an overview of the code, in what order should I look at
     things?
   - What are the most important top-level modules, and what is the
     overall flow of information between them?
   - "If I want to add <common sort of thing to add>, where do I look?"

-------------------------------------------------------------------------
# Useful recipies

## To add a .mli file for a given .ml file

`cd backend/cn`

`(cd ../..; dune exec -- ocaml-print-intf backend/cn/XXXXX.ml) > XXXXX.mli`

inspect XXXXX.mli to make sure that it looks semi-reasonable

`make -C ../.. cn`

inspect XXXXX.mli more closely

  - remove instances of `Dune__exe.`

  - if you see something like

       module SymSet :
         sig
           ... enormous amount of stuff

    replace it with

       module SymSet = Set.Make(Sym)

    You may need to add a bit more information to help typechecking --
    e.g., in setup.mli we have

       module StringSet : Set.S with type elt = string

  - Go through the .mli file and try to remove as many declarations as
    possible

  - Add a header, if you have enough information to write one.
    Headers look like this:

       (* Module Locations -- Utility functions for Cerberus locations

          This module adds a number of useful functions on locations to the
          ones already provided by Cerberus. *)

    If not, add a comment noting that it needs a header.  Comments
    should look like this:

       (* TODO: BCP: Describe what's needed... *)

  - Leave comments about anything else that needs a look from others

  - Recompile again to make sure nothing is broken

## To rebuild the dependency diagram of the CN codebase:

codept backend/cn/*.ml -dot > cn-modules.dot
dot -Tpdf -O -x cn-modules.dot

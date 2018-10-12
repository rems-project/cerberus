Cerberus
========

Cerberus is a tool for exploring the semantics of the C programming
language.  C remains central to our computing infrastructure but still
lacks a clear and complete semantics. Programmers lack tools to
explore the range of behaviours they should expect; compiler
development lacks test oracles; and formal verification and analysis
must make (explicitly or implicitly) many choices about the specific C
they target. The ISO standards for C have been developed over many
years but they remain unclear in some important respects, and in some
areas there are differences between the properties of C that are
relied on by the corpus of systems code in production, the properties
that compiler implementers aim to provide, and the properties of C as
it is specified in ISO C11.

The [Cerberus project](http://www.cl.cam.ac.uk/users/pes20/cerberus)
is developing semantic models for a substantial fragment of C.  More
details, including academic and ISO WG14 papers, are available on the
project web page.  Cerberus has several distinctive features:

* Where the ISO C11 standard is clear and corresponds with practice,
  Cerberus aims to follow that.

* Where there are differences, chiefly in the *memory layout model*
  (the behaviour of pointers, pointer arithmetic, uninitialised
  values, etc.), we aim to clarify the de facto standards,
  understand how the ISO standard could be reconciled with them,
  and provide options that capture both.

* Cerberus precisely defines a range of allowed behaviour, not just
  that of some specific implementation, with a combination of loose
  (but precise) specification, e.g. for evaluation order, and
  parameterisation (e.g. for integer type sizes).

* Cerberus is executable as a test oracle, to explore either all
  behaviours or single paths of small test programs.  It should be
  able to identify all undefined behaviours for these except
  nonterminating loops.  It can thus be used as a reference for
  discussion and for understanding the standard.  It should also be
  usable in the future as an oracle for compiler testing.  It is not an analysis
  tool for production C code.

* The semantics is factored via a translation into a simple Core
  language, to make it readable and conceptually and mathematically
  tractable; the dynamic semantics of Core can be linked with various
  sequential memory object models.  We currently have two such models:
  a symbolic model, in which allocation addresses are maintained
  symbolically and execution accumulates constraints on them (with
  Z3), and a concrete model, using a specific allocator.

* Its front-end is written from scratch to closely follow the C11
  standard, including a parser that follows the C11 standard grammar,
  and a typechecker.

*  We intend to make Cerberus open-source in due course. 

This is a step towards a clear, consistent, and unambiguous semantics for C.


Caveats and limitations
-----------------------

Our model covers many features of C, both syntactic and
semantic, but to keep the problem manageable we exclude some important
aspects.  We do not currently attempt to cover preprocessor features,
C11 character-set features, floating-point and complex types (beyond
simple float constants), user-defined variadic functions (we do cover
`printf`), bitfields, `volatile`, `restrict`, generic selection,
`register`, flexible array members, some exotic initialisation forms,
signals, `longjmp`, multiple translation units, most of the standard
library, or concurrency.  

Cerberus was originally designed to be integrated with the operational
model for C11 concurrency by Nienhuis, which has a mechanised proof of
equivalence to the axiomatic C11 model of Batty et al.  That
integration worked in a previous version, but it is not currently
supported or maintained.

We focus on the C commonly used for mainstream systems programming
without effective types, with `-fno-strict-aliasing`.  We are not
trying to cover every conceivable C implementation, or those on exotic
architectures.

Our semantics is intended as a source semantics for C.  For an
intermediate language, e.g. LLVM, there are related but distinct
goals.

Our implementation and web tool are intended to
explore the behaviour of small test cases, which is already
challenging, not as a bug-finding tool for production C code, which
would need considerably higher performance and coverage.  

Finally, while we have done significant testing and validation, more
would always be desirable; Cerberus is work in progress, not a
completely finished system.


Getting started with the web interface
--------------------------------------

### Loading a program

Load a test program, either by uploading a C file in `File > Load from file` or
by writing a test program directly. We also have lists of tests that
illustrate corner cases of the semantics, you can load these in `File > Load
defacto test` and `File > Load demo test`.

### Elaboration

Cerberus will immediately try to translate the code into Core, a functional
intermediate representation, and show it in a different tab.  Core is intended
to be as minimal as possible while remaining a suitable target for the
elaboration, and with the behaviour of Core programs made as explicit as
possible. For further information about Core, please check [Papers](#papers).

Moving the cursor in either the C source or Core tabs will highlight the corresponding C source and Core code.
The colouring behaviour can be changed in `Settings > Colour` and `Settings >
Colour Cursor`.

![](img/return.png)

![](img/core_return.png)

In this little example, the translation into Core binds a pure specified value `42` into the
label `a_81`, then kills the reference `x`, since it is going out of scope,
converts the value in `a_81` to a `signed int` and finally returns the
corresponding value.

The interface also allows you to see the abstract syntax tree of all the
Cerberus pipeline: Cabs (C Abstract) and Ail (Abstract Intermediate Language).
One can check them in `Elaborate > Cabs` and `Elaborate > Ail`.

![](img/ail.png)

Whenever possible, Ail and Core ASTs may contain _ISO C standard annotations_.
These justify the type-checking and elaboration. One can readily read the
relevant part of the standard by clicking on it.

### Execution

Cerberus is a executable semantics.  There are three execution mode in
Cerberus: `Random`, `Exhaustive` and `Interactive`. In random mode Cerberus pseudorandomly explores a single allowed
execution path; in exhaustive mode it performs an exhaustive search for
all allowed executions; and in interactive mode the user can step forwards and back through the execution(s).  In each mode, it can detect undefined behaviours on the explored 
execution path(s).

![](img/exec.png)

In our previous example, when running Cerberus in exhaustive mode, two outcomes
are possible: the conditional at line `3` is randomly evaluated to `true` or
`false`, since `x` is an `undefined value`.

### Compiling

The Cerberus UI is integrated with Matt Godbolt's [Compiler
Explorer](https://godbolt.org): the `Compile (Godbolt)` button lets one can immediately check the compilation by
major compilers (including Clang, GCC, ICC, and MSVC) to different targets (including x86 and ARM).


People
------

Contributors:

* Kayvan Memarian
* Victor B. F. Gomes
* Kyndylan Nienhuis
* Justus Matthiesen
* James Lingard
* David Chisnall
* Robert N. M. Watson
* Peter Sewell

The current main developers are Kayvan Memarian and Victor Gomes.
Cerberus originated with Justus Matthiesen's 2010-11 Part II project
dissertation and his 2011-12 MPhil dissertation; James Lingard's 2013-14 MPhil
dissertation developed a certifying translation validator for simple C programs
for the Clang front-end, w.r.t. the Cerberus and Vellvm semantics.


Funding
-------

This work is funded by [REMS: Rigorous Engineering of Mainstream
Systems](http://www.cl.cam.ac.uk/~pes20/rems), EPSRC Programme Grant
EP/K008528/1, EPSRC grant EP/H005633 (Leadership Fellowship, Sewell),
and a Gates Cambridge Scholarship (Nienhuis). This work is also part
of the CTSRD projects sponsored by the Defense Advanced Research
Projects Agency (DARPA) and the Air Force Research Laboratory (AFRL),
under contract FA8750-10-C-0237. The views, opinions, and/or findings
contained in this paper are those of the authors and should not be
interpreted as representing the official views or policies, either
expressed or implied, of the Department of Defense or the U.S.
Government.

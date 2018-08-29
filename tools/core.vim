" Vim syntax file
" Language: Core
" Maintainer: Victor Gomes
" Latest Revision: 29 August 2018

" Keywords
syn keyword keywords def fun proc ailname
syn keyword others if then else let in case of end pcall undef error pure eff strong weak array_shift member_shift

syn keyword types boolean integer floating struct union array ctype pointer
syn keyword loaded loaded
syn region ctype start="'" end="'"

syn keyword ctor Specified Unspecified Array

" Integers and floats
syn match number '\<\d\+\>'
syn match number '\<\d\+\.\d*\>'
syn keyword bool Unit True False NULL

" Identifier
syn match ident '\<\h*\>'

" Line comment
syn match lineComment '--.*$'

" Comment
syn region comment start="{-" end="-}"

" Undef and errors
syn region error start="<<" end=">>"
syn region error start="<<<" end=">>>"


" Highlight
"
hi def link number      Number
hi def link bool        Boolean

hi def link keywords    Keyword
hi def link others      Statement

hi def link types       Type
hi def link ctype       Type
hi def link loaded      StorageClass

hi def link lineComment Comment
hi def link comment     Comment

hi def link ctor        PreProc

hi def link error       Special

hi def link ident       Identifier

let b:current_syntax = "core"

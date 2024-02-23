" Quit when a (custom) syntax file was already loaded
if exists("b:current_syntax")
  finish
endif

syn case match

" Keywords
syn keyword     luvKeyword       and
syn keyword     luvKeyword       as
syn keyword     luvKeyword       assert
syn keyword     luvKeyword       break
syn keyword     luvKeyword       check
syn keyword     luvKeyword       continue
syn keyword     luvKeyword       def
syn keyword     luvKeyword       del
syn keyword     luvKeyword       elif
syn keyword     luvKeyword       else
syn keyword     luvKeyword       external
syn keyword     luvKeyword       false
syn keyword     luvKeyword       for
syn keyword     luvKeyword       from
syn keyword     luvKeyword       if
syn keyword     luvKeyword       import
syn keyword     luvKeyword       import_macros
syn keyword     luvKeyword       in
syn keyword     luvKeyword       macro
syn keyword     luvKeyword       not
syn keyword     luvKeyword       nonlocal
syn keyword     luvKeyword       null
syn keyword     luvKeyword       on
syn keyword     luvKeyword       or
syn keyword     luvKeyword       pass
syn keyword     luvKeyword       quote
syn keyword     luvKeyword       return
syn keyword     luvKeyword       sizeof
syn keyword     luvKeyword       struct
syn keyword     luvKeyword       true
syn keyword     luvKeyword       union
syn keyword     luvKeyword       while
syn keyword     luvKeyword       with
syn keyword     luvKeyword       zeroed
hi def link     luvKeyword       Keyword

" Basic type declarations
syn keyword     luvType bool byte rune int float
syn keyword     luvType u8 u16 u32 u64 i8 i16 i32 i64
syn keyword     luvType f16 f32 f64
syn keyword     luvType str
syn keyword     luvType void
hi def link     luvType Type

syn keyword     luvBuiltin range iter next stack heap enumerate print
hi def link     luvBuiltin Function

syn keyword     luvMacroHelper parse_expr parse_toplevel insert_global have_global args
hi def link     luvMacroHelper PreProc

syn region	luvPreProc	start="^\s*\zs\%(%:\|#\)" skip="\\$" end="$" keepend contains=ALLBUT,@Spell
syn region	luvPreProc	start="\%(%:\|#\){" end="}" keepend contains=ALLBUT,@Spell,luvPreProc
hi def link luvPreProc PreProc

" Strings
syn region  luvString matchgroup=luvQuotes
      \ start=+[f]\=\z(['"]\)+ end="\z1" skip="\\\\\|\\\z1"
      \ contains=luvEscape,@Spell
syn region  luvString matchgroup=luvTripleQuotes
      \ start=+[f]\=\z('''\|"""\)+ end="\z1" keepend
      \ contains=luvEscape,@Spell

syn match   luvEscape	+\\[abfnrtv'"\\]+ contained
syn match   luvEscape	"\\\o\{1,3}" contained
syn match   luvEscape	"\\x\x\{2}" contained
syn match   luvEscape	"\%(\\u\x\{4}\|\\U\x\{8}\)" contained
syn match   luvEscape	"\\$"

hi def link luvQuotes		      String
hi def link luvTripleQuotes		luvQuotes


hi def link     luvString            String
hi def link     luvTargetName        Special

" Comments
syn keyword     luvTodo              contained TODO FIXME XXX BUG NOTE
syn cluster     luvCommentGroup      contains=luvTodo
syn region      luvComment           start="//" end="$" contains=@luvCommentGroup,@Spell

hi def link     luvComment           Comment
hi def link     luvTodo              Todo

syn sync minlines=500

let b:current_syntax = "luv"

" Quit when a (custom) syntax file was already loaded
if exists("b:current_syntax")
  finish
endif

syn case match

" Keywords
syn keyword     luvKeyword       and
syn keyword     luvKeyword       block
syn keyword     luvKeyword       break
syn keyword     luvKeyword       check
syn keyword     luvKeyword       continue
syn keyword     luvKeyword       def
syn keyword     luvKeyword       elif
syn keyword     luvKeyword       else
syn keyword     luvKeyword       false
syn keyword     luvKeyword       for
syn keyword     luvKeyword       if
syn keyword     luvKeyword       in
syn keyword     luvKeyword       not
syn keyword     luvKeyword       nonlocal
syn keyword     luvKeyword       null
syn keyword     luvKeyword       or
syn keyword     luvKeyword       pass
syn keyword     luvKeyword       print
syn keyword     luvKeyword       return
syn keyword     luvKeyword       scoped
syn keyword     luvKeyword       struct
syn keyword     luvKeyword       true
syn keyword     luvKeyword       union
hi def link     luvKeyword       Keyword

" Basic type declarations
syn keyword     luvType bool byte rune int float
syn keyword     luvType u8 u16 u32 u64 i8 i16 i32 i64
syn keyword     luvType f16 f32 f64
syn keyword     luvType str
syn keyword     luvType void
hi def link     luvType Type

syn region	luvPreProc	start="^\s*\zs\%(%:\|#\)" skip="\\$" end="$" keepend contains=ALLBUT,@Spell
syn region	luvPreProc	start="\%(%:\|#\){" end="}" keepend contains=ALLBUT,@Spell,luvPreProc
hi def link luvPreProc PreProc

" Strings
syn region      luvString start=+L\="+ skip=+\\\\\|\\"+ end=+"+ contains=@Spell,luvTargetName
syn match       luvTargetName '\v:[^"]+' contained
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

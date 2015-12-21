exception TimeOut_P
exception TimeOut_T
exception TimeOut_S
exception Impossible_case
exception Impossible_case_search
exception LexErr of string
exception ParseErr of string
val error : string -> Lexing.position -> Lexing.position -> string
val lex_error : Lexing.lexbuf -> 'a
val parse_error : string -> 'a

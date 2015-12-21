open Parsing
open Lexing

exception TimeOut_P
exception TimeOut_T
exception TimeOut_S
exception Impossible_case
exception Impossible_case_search
exception LexErr of string
exception ParseErr of string;;

let error msg start finish = Printf.sprintf "(line %d: char %d..%d) : %s" 
     start.pos_lnum (start.pos_cnum - start.pos_bol) (finish.pos_cnum - finish.pos_bol) msg;;
	
let lex_error lexbuf = 
	raise (LexErr (error (lexeme lexbuf) (lexeme_start_p lexbuf) (lexeme_end_p lexbuf)));;
	
	
let parse_error msg = 
	raise (ParseErr (error msg (rhs_start_pos 1) (rhs_end_pos 1)));;



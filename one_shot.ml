open Global
open Pretty_printer
open Vertex_state
open Modules

(* ------------------------   Result Display ------------------------ *)
let print_result_web sat vertex0 =
	if not sat then Graph_tableau.remove_vertex tableau vertex0; 
	let (nb_pst,nb_st) = Graph_tableau.fold_vertex (fun v (x,y) -> if v.category = V_Prestate then (x+1,y) else (x,y+1)) tableau (0,0) in
	statistic := !statistic ^ ";" ^ string_of_int nb_pst ^ ";" ^ string_of_int nb_st;
	print_endline ("#D#" ^ !statistic);
  print_endline ("#R#The formula is " ^ (if sat then "satisfiable" else "unsatisfiable") ^ ".");
  print_endline "#T#";
  print_graph tableau "web";;
 
let result str_frm = 
 try 
    let lexbuf = Lexing.from_string str_frm in
     let set_frm = Parser_formula.main Lexer_formula.token lexbuf in
		 print_endline ("#A#" ^ Pretty_printer.string_of_formulae set_frm "web");
						 is_satisfiable set_frm "web";	
  with 
    | Except.LexErr n -> print_endline ("#E#" ^ n ^ ": a problem has occurred during lexing. Please check your formula."); exit 0
    | Parsing.Parse_error -> print_endline "#E#A problem has occurred during parsing. Please check your formula."; exit 0
		| Except.ParseErr str->  print_endline (str);  print_endline "#E#A problem has occurred during parsing. Please check your formula."; exit 0
    | Except.Impossible_case -> print_endline "#E#Cas impossible"; exit 0
		| _ -> print_endline "#E#An unexpected error has occurred."; exit 0
	;;

(* --------------------------  main function ------------------------ *)
let main () =
if Array.length Sys.argv > 0 then
  let (vertex0,sat) = result Sys.argv.(1) in 
      print_result_web sat vertex0;print_endline ("#C#" ^ string_of_float (Sys.time() -. !time_start));
else print_endline "#E#Attention, no input parameter.\n";;

let _ = main ();

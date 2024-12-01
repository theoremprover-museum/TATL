open Global
open Vertex_state
open Pretty_printer
open Modules

(***************************************************************************************)
(*                                     Result Display                                  *)
(***************************************************************************************)

let print_result_line sat vertex0 = 
	
	if not sat then Graph_tableau.remove_vertex tableau vertex0;
	let (nb_pst,nb_st) = Graph_tableau.fold_vertex (fun v (x,y) -> if v.category = V_Prestate then (x+1,y) else (x,y+1)) tableau (0,0) in
	print_endline ("nb_prestate final tableau: " ^  (string_of_int nb_pst) ^ "\nnb_state final tableau:" ^ (string_of_int nb_st));
	print_newline();
	if !verbatim then(
  print_endline "*";
  print_endline "* Final Tableau ";
  print_endline "*************** "; print_newline();
  print_graph tableau "line"); 
	print_newline();
	print_endline "*"; 
  print_string "* The formula is "; 
  if sat then print_string "satisfiable" else print_string "unsatisfiable"; print_endline ".";
	print_endline "*"; print_newline();
	let _frm = Pretty_printer.string_of_formulae (vertex0.ens_frm) "line" in
 (* Graphviz.graphviz_tableau "fichiers/tab_final.gv" frm;*)
	print_string "Fin de la procedure : "; print_endline (string_of_float (Sys.time() -. !time_start));;



 (* let extract_model vertex0 =  *)
 (*    	let toto = Synthesis.synthesis vertex0 in *)
 (*    	let frm = Pretty_printer.string_of_formulae (vertex0.ens_frm) "line" in *)
 (*    	Graphviz.graphviz_model_prop "fichiers/extracted_model.gv" frm *)

(***************************************************************************************)
(*                             Display functions                                       *)
(***************************************************************************************)

            (*---------------- Displayed at Beggining ----------------*)

let print_entete ()= 
   print_endline "         ----------------------------------------------";
   print_endline "         |          TATL* : Tableaux for ATL*         |";
   print_endline "         |          Amelie David - Lab. IBISC         |";
   print_endline "         |     23 bd de France -  91037 Evry Cedex    |";
   print_endline "         ----------------------------------------------";
   print_newline() ;;
      
(* let print_options() =   *)
(*    print_newline(); *)
(*    print_endline "Options:"; *)
(*    print_endline "--------"; *)
(*    print_endline "1) Enter a formula"; *)
(*    print_endline "2) Close"; *)
(*    print_newline(); *)
(*    print_string "Your choice?  ";; *)
   
            (*---------------- satisfiability result ----------------*)

let satisfiability_result str_frm = 
  try 
     let lexbuf = Lexing.from_string str_frm in 
     let set_frm = Parser_formula.main Lexer_formula.token lexbuf in
		 print_endline (Pretty_printer.string_of_formulae set_frm "line");
		(*let toto = read_int () in *) 
						 is_satisfiable set_frm "line";					
  with
    | Except.LexErr n -> print_endline ("Error " ^ n ^ ": a problem has occurred during lexing. Please check your formula."); exit 0
    | Parsing.Parse_error -> print_endline "Error : a problem has occurred during parsing. Please check your formula."; exit 0
		| Except.ParseErr str->  print_endline str;  print_endline "Error : a problem has occurred during parsing. Please check your formula."; exit 0
    | Except.Impossible_case -> print_endline "Error : Cas impossible"; exit 0
		| _ -> print_endline "Error : an unexpected error has occurred."; exit 0

         
            (*---------------- Treatment of the first menu  ----------------*)

(* let rec ask_choice () = *)
(*   print_options(); *)
(*   let choice = read_line() in match choice with *)
(*    | "1" -> print_endline "Enter a formula:  " ; *)
(* 		     time_start := Sys.time(); *)
(*          let frm = read_line() in let (vertex0,sat) = satisfiability_result frm  in  *)
(*                   print_result_line sat vertex0 ; *)
(* 									(\*if sat then extract_model vertex0;*\) *)
(* 									let nb1 = generator_state true and nb2 = generator_pre_state true in clear_all() *)
(*    | "2" -> raise Exit; *)
(*    | _ -> ask_choice();; *)

let print_begin () =
   print_entete ();
   try
      while true do
				(*ask_choice ();*)
        print_endline "Enter a formula:  " ;
		     time_start := Sys.time();
         let frm = read_line() in let (vertex0,sat) = satisfiability_result frm  in 
                  print_result_line sat vertex0 ;
									(*if sat then extract_model vertex0;*)
									let _nb1 = generator_state true and _nb2 = generator_pre_state true in clear_all()
      done
   with Exit -> print_endline "--- END ---" ;;

(***************************************************************************************)
(*                             Treatment of the command line                           *)
(***************************************************************************************)

let one_shot = ref false
let frm = ref ""
 
let usage = "usage: (1) " ^  Sys.argv.(0) ^ " [-v] \n       (2) " ^  Sys.argv.(0) ^" -o [-v] [-f string] \n"
 
let speclist = [
    ("-o", Arg.Unit   (fun () -> one_shot := true),  ": for one shot mode");
		("-v", Arg.Unit   (fun () -> verbatim := true),  ": to obtain the initial and final tableau (verbatim mode)");
    ("-f", Arg.String (fun f -> frm := f),         ": input formula in one shot mode ");
  ] 
   
(***************************************************************************************)
(*                                    Main Program                                     *)
(***************************************************************************************)
let funct_one_shot frm =    
   print_entete();
   let (vertex0,sat) =  satisfiability_result frm in
     print_result_line sat vertex0 ; 
		 print_endline (string_of_float (Sys.time() -. !time_start));
		 (*if sat then extract_model vertex0*);;

let () =
  Random.self_init ();
  (* Read the arguments *)
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;      
      if !one_shot then funct_one_shot !frm
       else print_begin ()
;;





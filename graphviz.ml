open Modules
open Global
open Synthesis

let h_rename_event = Hashtbl.create(40);;
Hashtbl.add h_rename_event "" Top; Hashtbl.clear h_rename_event;; 
let generator_rename = let compt  = counter_since 1  in fun r ->  string_of_int(compt r)

let rename_eventualities ens_event = 
	State_Formulae.fold (
		fun e ens -> 	
		try 
			let new_name = Hashtbl.find h_rename_event (Pretty_printer.string_of_formula e "line")
		  in State_Formulae.add new_name ens
		with Not_found ->  
			let new_name = Prop ("E"^generator_rename false) in 
      Hashtbl.add h_rename_event (Pretty_printer.string_of_formula e "line") new_name;
			State_Formulae.add new_name ens
		) ens_event State_Formulae.empty


let get_lst_node_egde () =
	Graph_tableau.fold_vertex (
		fun v (str_state,str_prestates, lst_edge, lst_move_edge) ->
			if v.category = V_State then 
				let new_str_state = str_state ^ " " ^ v.name in 
				let new_lst_move_edge = Graph_tableau.fold_succ_e ( 
					fun e lst -> (v.name, (Graph_tableau.E.dst e).name, rename_eventualities (Graph_tableau.E.label e).event_e)::lst
					) tableau v lst_move_edge in 
				(new_str_state,str_prestates,lst_edge, new_lst_move_edge)
		  else  
				let new_lst_edge = Graph_tableau.fold_succ_e ( 
					fun e lst -> (v.name, (Graph_tableau.E.dst e).name, rename_eventualities (Graph_tableau.E.label e).event_e)::lst
					) tableau v lst_edge in
			if v.name = "PO" then
					(str_state,str_prestates, new_lst_edge, lst_move_edge)
			else
				let new_str_prestate = str_prestates ^ " " ^ v.name in  
				(str_state,new_str_prestate,new_lst_edge,lst_move_edge)
	) tableau ("","",[],[])

let rec string_of_succ lst = match lst with
| [] -> "";
| s::q -> (string_of_succ q) ^ " " ^ (Graph_tableau.V.label s).name
	
let rec output_string_edge fic lst = match lst with
| [] -> ()
| (v,l)::q -> let str = string_of_succ l in 
  (output_string fic (v ^ " -> {" ^ str ^ "}\n"); output_string_edge fic q) 
	
let rec output_string_move_edge fic lst = match lst with
| [] -> ()
| (s,d,t)::q -> (output_string fic (s ^ " -> " ^ d ^ " [label=\"" ^ (Pretty_printer.string_of_movecs t "line") ^ "\"]\n"); (* labeltooltip *)
	   output_string_move_edge fic q) 

let rec output_string_event fic lst = match lst with
| [] -> ()
| (s,d,t)::q -> (output_string fic (s ^ " -> " ^ d ^ " [label=\"" ^ (Pretty_printer.string_of_formulae t "line") ^ "\"]\n"); (* labeltooltip *)
	   output_string_event fic q) 
	 	
let graphviz_tableau nfic frm =
	let (str_state,str_prestate, lst_edge, lst_move_edge) = get_lst_node_egde() in
	let fic = open_out nfic in
	output_string fic "digraph g {\n" ; 
	output_string fic ("{node [shape=box,style=filled,fillcolor=pink];\n 1 [label=\""^ String.escaped frm ^ "\"]}\n");
	output_string fic ("{node [shape=box,style=filled,fillcolor=aquamarine];\n P0}\n");
	output_string fic ("{node [shape=ellipse];\n" ^ str_state ^ "}\n"); 
	output_string fic ("{node [shape=square];\n"^ str_prestate ^ "}\n");
	output_string fic ("{edge [arrowsize=2, color=crimson, style=dashed];\n") ;
	output_string_event fic lst_edge;
	output_string fic ("}\n {edge [arrowsize=1, color=black];\n");
	output_string_event fic lst_move_edge ;
	output_string fic "}}";
	close_out fic ;;


(*********** A partir d'ici, c'est pour l'extraction de modèle *************) 

let get_lst_node_egde_model () =
	Graph_model.fold_vertex (
		fun v (str_init, str_node, lst_move_edge) ->
				if v.name_node = "n1" then 
					let new_lst_move_edge = Graph_model.fold_succ_e ( 
					 fun e lst -> (v.name_node, (Graph_model.E.dst e).name_node, (Graph_model.E.label e).vector)::lst
					 ) model v lst_move_edge in 
					(v.name_node ^ " [label=\""^ v.name_node ^ " (" ^ (Pretty_printer.string_of_formulae v.prop "line") ^ ")\"]\n", str_node, new_lst_move_edge)
				else
				  let new_str_node = str_node ^ " " ^ v.name_node ^ " [label=\""^ v.name_node ^ " (" ^ (Pretty_printer.string_of_formulae v.prop "line") ^ ")\"]\n" in 
			    let new_lst_move_edge = Graph_model.fold_succ_e ( 
					 fun e lst -> (v.name_node, (Graph_model.E.dst e).name_node, (Graph_model.E.label e).vector)::lst
					 ) model v lst_move_edge in 
				 (str_init, new_str_node, new_lst_move_edge)
	) model ("","",[])
	
	let get_lst_node_egde_model_state () =
	Graph_model.fold_vertex (
		fun v (str_init, str_node, lst_move_edge) ->
				if v.name_node = "n1" then 
					let new_lst_move_edge = Graph_model.fold_succ_e ( 
					 fun e lst -> (v.name_node, (Graph_model.E.dst e).name_node, (Graph_model.E.label e).vector)::lst
					 ) model v lst_move_edge in 
					(v.name_node ^ " [label=\""^ v.name_node ^ "(" ^ v.name_state ^ ")\"]\n", str_node, new_lst_move_edge)
				else
				  let new_str_node = str_node ^ " " ^ v.name_node ^ " [label=\""^ v.name_node ^ "(" ^ v.name_state ^ ")\"]\n" in 
			    let new_lst_move_edge = Graph_model.fold_succ_e ( 
					 fun e lst -> (v.name_node, (Graph_model.E.dst e).name_node, (Graph_model.E.label e).vector)::lst
					 ) model v lst_move_edge in 
				 (str_init, new_str_node, new_lst_move_edge)
	) model ("","",[])


 let graphviz_model_prop nfic frm = 
  let (str_init, str_node,lst_move_edge) = get_lst_node_egde_model() in
	let fic = open_out nfic in
	output_string fic "digraph g {\n" ;
	output_string fic ("{node [shape=box,style=filled,fillcolor=pink];\n 1 [label=\""^ String.escaped frm ^ "\"]}\n");
	output_string fic ("{node [shape=box,style=filled,fillcolor=aquamarine];\n " ^  str_init ^ "}\n");
	output_string fic ("{node [shape=ellipse];\n" ^ str_node ^ "}\n");
	output_string fic ("{edge [arrowsize=1, color=black];\n");
	output_string_move_edge fic lst_move_edge;
	output_string fic "}}";
	close_out fic ;;

let graphviz_model_state nfic frm = 
  let (str_init, str_node,lst_move_edge) = get_lst_node_egde_model_state() in
	let fic = open_out nfic in
	output_string fic "digraph g {\n" ;
	output_string fic ("{node [shape=box,style=filled,fillcolor=pink];\n 1 [label=\""^ String.escaped frm ^ "\"]}\n");
	output_string fic ("{node [shape=box,style=filled,fillcolor=aquamarine];\n " ^ str_init ^ "}\n");
	output_string fic ("{node [shape=ellipse];\n" ^ str_node ^ "}\n");
	output_string fic ("{edge [arrowsize=1, color=black];\n");
	output_string_move_edge fic lst_move_edge;
	output_string fic "}}";
	close_out fic ;;
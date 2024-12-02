open Modules
open Global

(* Method to extract model from ATL and ATL+ tableau *)
(* Amélie DAVID and Fabio PAPACCHINI *)

type couleur = BLANC | GRIS | NOIR;;

let h_couleur = Hashtbl.create(500);;
Hashtbl.add h_couleur "" BLANC; Hashtbl.clear h_couleur;; 

let h_st_tab_mod = Hashtbl.create(500);;
Hashtbl.add h_st_tab_mod "" {name_node=""; name_state=""; prop=State_Formulae.empty} ; Hashtbl.clear h_st_tab_mod;;

let print_debug_couleur c = match c with
| BLANC -> "Blanc"
| GRIS -> "Gris"
| NOIR -> "Noir"

let print_debug_lst_pred lst_edge = 
	print_endline ("[debug] lst_pred :");
	let rec print lst = match lst with
	| [] -> print_newline()
	| [e] -> let u = Graph_tableau.E.src e and v = Graph_tableau.E.dst e in print_endline (v.name ^ ":" ^ u.name)
	| e::q -> let u = Graph_tableau.E.src e and v = Graph_tableau.E.dst e in print_string (v.name ^ ":" ^ u.name ^ " | " ) ; print q
in print lst_edge

let print_debug_lst_circuit lst_circuit = 
	print_endline ("[debug] lst_circuit :");
	let rec print lst = match lst with
	| [] -> print_newline()
	| [e] -> let u = Graph_tableau.E.src e and v= Graph_tableau.E.dst e in  print_endline (v.name ^ ":" ^ u.name)
	| e::q -> let u = Graph_tableau.E.src e and v = Graph_tableau.E.dst e in print_string (v.name ^ ":" ^ u.name ^ " | ") ; print q
  in let rec  print_one_circuit lst = match lst with
	| [] -> print_newline()
	| [c] -> print c
	| c::q -> print c;  print_one_circuit q
in print_one_circuit lst_circuit

let debug_lst_edge lst_edge = 
	let rec print lst = match lst with
	| [] -> ""
	| e::q -> let u = Graph_tableau.E.src e and v = Graph_tableau.E.dst e in (v.name ^ ":" ^  u.name) ^ " | " ^ print q 
in print lst_edge

let search_pred u lst_edge = 
	let rec search lst = match lst with
	| [] -> raise Not_found
	| e::_ when u= Graph_tableau.E.dst e -> e
	| _::q -> search q
in search lst_edge 

let  detect_circuit lst_edge e =
	let u = Graph_tableau.E.src e and v = Graph_tableau.E.dst e in  
	let rec detect u circuit =
		let edge = search_pred u lst_edge in 
		let u_prime = Graph_tableau.E.src edge in
		if u_prime = v then
		 edge::circuit
		else
		 detect u_prime (edge::circuit)
	in detect u []
	
let rec visit_depth_first_search node lst_edge lst_circuit = 
	Hashtbl.remove h_couleur node.name ;
	Hashtbl.add h_couleur node.name GRIS ;
	let (lst_new_edge,lst_new_circuit) = Graph_tableau.fold_succ_e (
		fun e (lst,lst2) -> 
			let succ = Graph_tableau.E.dst e in 
			let c = Hashtbl.find h_couleur succ.name in 
		if c = BLANC then 
			let (lst_edge,lst_circuit) = visit_depth_first_search succ (e::lst) lst2 in	(lst_edge,lst_circuit)
		else if c= GRIS then   (* We found a circuit *)
			let one_circuit = detect_circuit lst e in (lst, (e::one_circuit)::lst_circuit) 
		else (lst,lst2)
	) tableau node (lst_edge,lst_circuit) in
	Hashtbl.remove h_couleur node.name;
	Hashtbl.add h_couleur node.name NOIR;
	(lst_new_edge,lst_new_circuit)
	
(* depth-firt search implementation *)
let search_circuit init_prestate =
	Hashtbl.clear h_couleur;
	Graph_tableau.iter_vertex (
		fun v -> Hashtbl.add h_couleur v.name BLANC 
	) tableau;
	let (_lst_pred,lst_circuit) = visit_depth_first_search init_prestate [] [] in 
	lst_circuit
	
	
let check_circuit circuit = 
	let event_circuit = (Graph_tableau.E.label (List.hd circuit)).event_e
  in 
	let rec check circuit ens_ev = 
		if State_Formulae.cardinal ens_ev = 0 then true else
			match circuit with
			| [] ->  if State_Formulae.cardinal ens_ev = 0 then true else false
			| e::q -> let ens_ev_to_comp = (Graph_tableau.E.label e).event_e in 
			          check q (State_Formulae.inter ens_ev ens_ev_to_comp)
	in  check circuit event_circuit
	
let suppr_edge circuit =
	List.iter (
				fun e -> if (Graph_tableau.E.src e).category = V_Prestate then Graph_tableau.remove_edge_e tableau e
		) circuit
		
let suppr_edge_invalid_circuit lst_circuit=
	let rec check_lst_circuit lst = match lst with
	| [] -> print_newline()
	| circuit::q when check_circuit circuit-> check_lst_circuit q 
	| circuit::q -> suppr_edge circuit; check_lst_circuit q
 in check_lst_circuit lst_circuit 
		
let get_proposition_state ens_frm = 
	State_Formulae.filter (fun frm -> match frm with 
	| Top | Prop _ | Neg (Prop _) -> true 
	| _ -> false 
	) ens_frm		
		
let rec visit_dfs state state_model = 
	Hashtbl.remove h_couleur state.name ;
	Hashtbl.add h_couleur state.name NOIR ;
  Graph_tableau.iter_succ_e (
		fun e -> 
			let succ = Graph_tableau.E.dst e in   (* succ is then a prestate *) 
			let c = Hashtbl.find h_couleur succ.name in 
		if c = BLANC then 
			(
			Hashtbl.remove h_couleur succ.name;
			Hashtbl.add h_couleur succ.name NOIR;
			let succ_chosen = List.hd (Graph_tableau.succ tableau succ) in (* here succ_model is a state *)
			Hashtbl.add h_prestate_default succ succ_chosen;
			let c_succ_chosen = Hashtbl.find h_couleur succ_chosen.name  in 
			let succ_model = if c_succ_chosen = NOIR then
				Hashtbl.find h_st_tab_mod succ_chosen.name
			else 
			  {name_node=generator_node false; name_state=succ_chosen.name; prop=get_proposition_state succ_chosen.ens_frm} 
			in 
			if c_succ_chosen = BLANC then Hashtbl.add h_st_tab_mod succ_chosen.name succ_model;
			Graph_model.add_vertex model succ_model ; 
			Graph_model.add_edge_e model (Graph_model.E.create state_model (Graph_tableau.E.label e) succ_model); 
			visit_dfs succ_chosen succ_model
			)
		else (
				let state_model_succ = Hashtbl.find h_st_tab_mod (Hashtbl.find h_prestate_default succ).name in 
				Graph_model.add_edge_e model (Graph_model.E.create state_model (Graph_tableau.E.label e) state_model_succ)
			)
	) tableau state
		
let extract_model init_prestate = 
	Hashtbl.clear h_couleur;
	Hashtbl.clear h_st_tab_mod;
	Graph_tableau.iter_vertex (
		fun v -> Hashtbl.add h_couleur v.name BLANC 
	) tableau;
	(* Initialisation of the first state *)
	let init_state = List.hd (Graph_tableau.succ tableau init_prestate) in 
	Hashtbl.add h_prestate_default init_prestate init_state;
	let init_node = {name_node="n1"; name_state=init_state.name; prop=get_proposition_state init_state.ens_frm} in
	    Hashtbl.add h_st_tab_mod init_state.name init_node;
			Graph_model.add_vertex  model init_node; 
			Hashtbl.remove h_couleur init_prestate.name;
			Hashtbl.add h_couleur init_prestate.name NOIR;	
	visit_dfs init_state init_node
	
	
 let nom_provisoire init_prestate = 
	let lst_circuit = search_circuit init_prestate in 
	suppr_edge_invalid_circuit lst_circuit;
 let frm = Pretty_printer.string_of_formulae (init_prestate.ens_frm) "line" in
		Graphviz.graphviz_tableau "fichiers/tab_inter_model.gv" frm;	
	extract_model init_prestate

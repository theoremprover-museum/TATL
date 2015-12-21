open Modules
open Global

let get_all_eventualities () =
	let ens_all_event = Graph_tableau.fold_vertex (
		fun v ens -> let ens_event = State_Formulae.filter (fun frm -> is_eventuality frm) v.ens_frm in State_Formulae.union ens ens_event
  ) tableau State_Formulae.empty
	in Array.of_list (State_Formulae.elements ens_all_event)

(* for the moment, I choose by default the first successor of the list of a prestate *)
let choose_state_default pstate = 
	try 
			Hashtbl.find h_prestate_default pstate
	with Not_found -> 
	 let choice = List.hd (Graph_tableau.succ tableau pstate) in 
	 Hashtbl.add h_prestate_default pstate choice; choice 
	
let num_start_a_event a_event node = 
	let length_a = Array.length a_event in
	if length_a = 0 then -1
	else 
	 let s_a_event = length_a in 
	 	let rec search index = if index=s_a_event then 0 else
		if State_Formulae.mem a_event.(index) (node.ens_frm) then 
			index
		else search (index + 1)
		in search 0

let get_proposition_state ens_frm = 
	State_Formulae.filter (fun frm -> match frm with 
	| Top | Prop _ | Neg (Prop _) -> true 
	| _ -> false 
	) ens_frm
	
let choose_state_ev prestate ev = 
	let rec choose last lst = match lst with
	| [] -> (last,false)
	| s::q -> if not(State_Formulae.mem ev s.ens_frm) || Elimination.is_imm_real (Elimination.get_tuple ev s.event) s.ens_frm s.name  
	         then (s,true) else choose s q
in let lst_succ = (Graph_tableau.succ tableau prestate) in 
   choose (List.hd lst_succ) lst_succ  
	
let rec construct_eventuality_tree_state node state ev = 
	(* pour chaque pré-état, on choisit un état, ici aussi, il faudra utiliser une hashtable  (prestate,ev -> state) *)
	Graph_tableau.fold_succ_e (
			fun e lst -> let dst = Graph_tableau.E.dst e and mv = Graph_tableau.E.label e in
				 let (choice,is_real) = choose_state_ev dst ev in
				 let next_node = {name_node = generator_node false ; name_state = choice.name; prop=get_proposition_state choice.ens_frm } in
				 let v_node = Graph_model.V.create next_node in 
				 Graph_model.add_edge_e model (Graph_model.E.create node mv v_node) ;
				(* Cas1, il existe un etat satisfaisant l'éventualité ou ne contenant pas l'éventualité *) 
				 if is_real then  
						(v_node,choice)::lst
	       (* Cas2, il n'existe pas de tel état et on doit relancer la construction de l'éventualité *)
				 else construct_eventuality_tree_state v_node choice ev
			) tableau state []
	
let rec analyse_level ev level lst_level = match lst_level with
| [] -> []
| (node,state)::q -> try
			let found_node = Hashtbl.find h_level_state (level,state.name) in 
			 Graph_model.iter_pred_e (fun edge -> 
				Graph_model.add_edge_e model (Graph_model.E.create (Graph_model.E.src edge) (Graph_model.E.label edge) found_node);
				Graph_model.remove_edge_e model edge;
				) model node;   
				Graph_model.remove_vertex model node;
				analyse_level ev level q
	with Not_found -> Hashtbl.add h_level_state (level,state.name) node; 
	(* Il faudra ajouter une hashtbl pour stocker les résultats déjà obtenus *)
	if level = -1 || not(State_Formulae.mem ev state.ens_frm) || Elimination.is_imm_real (Elimination.get_tuple ev state.event) state.ens_frm state.name then
	(* pour chaque pre-etat successeur, choisir un état successeur par défaut *)
	   Graph_tableau.fold_succ_e (
				fun e lst -> let dst = Graph_tableau.E.dst e and mv = Graph_tableau.E.label e in
				 let choice = choose_state_default dst in 
				 let next_node = {name_node = generator_node false ; name_state = choice.name; prop=get_proposition_state choice.ens_frm } in
				 let v_node = Graph_model.V.create next_node in 
				 Graph_model.add_edge_e model (Graph_model.E.create node mv v_node) ; (v_node,choice)::lst
			) tableau state (analyse_level ev level q)
 (* sinon trouver l'arbre de realisation pour l'etat et l'eventuality *)
  else 
     let deadlock = construct_eventuality_tree_state node state ev in deadlock@(analyse_level ev level q)

let analyse_all_level a_event start_a nb lst_level = 
	if List.length lst_level = 0 then
		lst_level 
	else
	if start_a = -1 then
		analyse_level Top start_a lst_level
	else
	let fin = if start_a = 0 then (nb - 1) else start_a - 1 in 
 	let rec analyse n lst_level = 
		let modulo = n mod nb in 
  	let new_lst_level = analyse_level a_event.(modulo) modulo lst_level in 
  	match modulo with
    | n1 when n1 = fin -> new_lst_level 
  	| _ ->  analyse (n+1) new_lst_level 
	in analyse start_a lst_level

let cycle_all_level a_event start_a nb lst_level  = 
	let rec cycle lst = 
	 let new_lst = analyse_all_level a_event start_a nb lst in 
	 if List.length new_lst > 0  then cycle new_lst
	in cycle lst_level
	
let synthesis init_prestate  = 
	let a_event = get_all_eventualities () and  init_state = choose_state_default init_prestate in 
	let start_a = num_start_a_event a_event init_state and 
	    init_node = {name_node="n1"; name_state=init_state.name; prop=get_proposition_state init_state.ens_frm} in
			Graph_model.add_vertex  model init_node; 
	let lst_level = [(init_node,init_state)] in  
	  print_string "Nb eventualities : " ; print_int (Array.length a_event); print_newline();
	  cycle_all_level a_event start_a (Array.length a_event) lst_level 

open Except
open Modules
open Global

(* On conserve le vertex 0 pour connaître les états initiaux *)

(******************************************************************)
(*                        States Elimination                      *)
(******************************************************************)

 let is_complet_succ v = let ens_succ_mv =  
		Graph_tableau.fold_succ_e (fun e ens_mv ->
			let label_e = Graph_tableau.E.label e in Movecs.union ens_mv label_e.vector
    ) tableau v Movecs.empty  
	 in Movecs.equal ens_succ_mv (Graph_tableau.V.label v).assoc_movecs
  

let is_imm_real ev ens_frm st_name =
	let rec real path_ev = match path_ev with
	| AndP(p1,p2) -> real p1 && real p2
	| OrP (p1,p2) -> real p1 || real p2
	| State(s) -> State_Formulae.mem s ens_frm || Path_Formulae.mem path_ev ev.path_frm
	| Next(_) -> true
	| Always(State(s)) -> State_Formulae.mem s ens_frm || Path_Formulae.mem (State s) ev.path_frm
	| Always(p1) -> Path_Formulae.mem p1 ev.path_frm 
	| Until(_,State(s)) -> State_Formulae.mem s ens_frm || Path_Formulae.mem (State s) ev.path_frm
	| Until(_,p2) -> Path_Formulae.mem p2 ev.path_frm
	| _ -> raise Impossible_case
  in let path = match ev.frm with 
	| Coal(_,p) | CoCoal(_,p) -> p 
	| _ -> raise Impossible_case  
	in let rep = real path in 
	(if rep then Hashtbl.add h_ev_st (ev.frm,st_name) 1 else Hashtbl.add h_ev_st (ev.frm,st_name) 2 );
	rep

let get_tuple frm lst_event = List.find (fun ev -> compare_formula ev.frm frm = 0) lst_event   
	
let get_ev_non_imm_real s = 
	List.fold_left (fun l ev -> 
		if is_imm_real ev s.ens_frm s.name then l else ev::l)[] s.event
	
	
let verif_edge s l_edge ev num_ev= 
	let mv_edge = Movecs.elements l_edge 
	and nb_pos = (Graph_tableau.V.label s).nb_pos
	and nb_neg = (Graph_tableau.V.label s).nb_neg in 
	let rec verif_mv mv la = match mv with
    |[] -> true
		| (a,m)::q -> if (not (Agents.mem a la)) || (m = num_ev) then verif_mv q la else false
	and  verif_pos lst la = match lst with
	| [] -> true
	| mv::q -> if verif_mv mv la then verif_pos q la else false
	and verif_neg lst la = match lst with
	| [] -> true
	| mv::q -> if Construction.function_co_sigma mv nb_pos nb_neg = num_ev && Agents.subset (Agents.diff !ag_all la) (Construction.function_n_sigma mv  nb_pos)
	  then verif_neg q la else false 
	in match ev.frm with
	| Coal (la, _) -> verif_pos mv_edge la
	| CoCoal (la, _) when Agents.equal la !ag_all -> true
	| CoCoal (la, _) -> verif_neg mv_edge la
	| _ -> raise Impossible_case

let get_num_next_ev next_ev lst_next_pos lst_next_neg =  match next_ev with
| Coal (la,_) -> fst (List.find (fun (_,b) -> compare_formula b (Coal(la,Next (State next_ev))) = 0) lst_next_pos)
| CoCoal (la, _) when Agents.equal la !ag_all -> -1
| CoCoal (la,_) -> fst (List.find (fun (_,b) -> compare_formula b (CoCoal(la,Next (State next_ev))) = 0) lst_next_neg)
| _ -> raise Impossible_case
	
let get_succ_to_be_verified ev s = Graph_tableau.fold_succ_e ( (* go through all vectors from s *)
		fun edge l ->
			let num_ev = get_num_next_ev ev.next_frm (Graph_tableau.V.label s).lst_next_pos (Graph_tableau.V.label s).lst_next_neg in
			let l_edge = Graph_tableau.E.label edge and prestate = Graph_tableau.E.dst edge in
			(* Does the prestate correspond to the eventuality to be verified *) 
				if is_eventuality ev.next_frm && (State_Formulae.mem ev.next_frm (Graph_tableau.V.label prestate).ens_frm) && (verif_edge s l_edge.vector ev num_ev) then
				let lst_ev_succ = Graph_tableau.fold_succ (
				  (* get all the states starting from a prestate. *)
					fun succ lst_s -> 	let ev_next = get_tuple ev.next_frm (Graph_tableau.V.label succ).event in 
					 (succ,ev_next)::lst_s
				) tableau prestate []
				in (prestate,lst_ev_succ)::l
				else l
		) tableau s []	
	
let update_hashtable_suppr s = 
	let label = Graph_tableau.V.label s in
	List.iter (fun ev -> Hashtbl.replace h_ev_st (ev.frm, label.name) 0) label.event

let update_hashtable_suppr_p p = 
	let label = Graph_tableau.V.label p in
	State_Formulae.iter (fun frm -> 
		match frm with 
		| Coal _ | CoCoal _ -> Hashtbl.replace h_ev_pst (frm, label.name) 0
		| _ -> ()
		) label.ens_frm
		
						
let rec remove_state s = 
	update_hashtable_suppr s;
	if not (Hashtbl.mem h_suppr s.name) then 
	(
  	Hashtbl.add h_suppr s.name "";
    Graph_tableau.iter_pred_e ( 
      fun e -> Graph_tableau.remove_edge_e tableau e 
    ) tableau s ;
  	Graph_tableau.iter_succ (
  		fun p -> if not (Hashtbl.mem h_suppr p.name) then
  			 let degree = (Graph_tableau.in_degree tableau p)  in 
  				if degree <= 1 then 
  					 remove_prestate p 
  	) tableau s ; 
    Graph_tableau.remove_vertex tableau s
	)
and remove_prestate p = 
	update_hashtable_suppr_p p;
	let c = Hashtbl.mem h_suppr p.name in
	if not c then 
	(
		Hashtbl.add h_suppr p.name "";
  	Graph_tableau.iter_pred (
  		fun s -> remove_state s
    ) tableau p ;
  	Graph_tableau.iter_succ ( 
  		fun s -> 
			let c = Hashtbl.mem h_suppr s.name in
			if not c then 
  			let degree = (Graph_tableau.in_degree tableau p) in 
  			if degree <= 1 then  remove_state s
  	) tableau p;
  	Graph_tableau.remove_vertex tableau p
	)

let rec verif_succ ev st= 
	let lst_prestate_succ = get_succ_to_be_verified ev st in 
	let rec verif_states lst = match lst with  (* One state has to be true *)
	| [] -> false
	| (s,e)::q -> 
		(* On check si on a déjà vérifié l'éventualité pour cet état *)
		try 
			let rep_find = Hashtbl.find h_ev_st (e.frm, s.name) in 
			  if rep_find = 1 then true else verif_states q
		with Not_found -> 
		if is_complet_succ s then (
  		let label=Graph_tableau.V.label s in 
  		if is_imm_real e label.ens_frm label.name then true 
			else if verif_succ e s then (Hashtbl.replace h_ev_st (e.frm, s.name) 1; true) else (Hashtbl.replace h_ev_st (e.frm, s.name) 0;verif_states q)
		)else ((Hashtbl.replace h_ev_st (e.frm, s.name) 0; remove_state s ; verif_states q))
	and verif_prestate lst_p_ev = 
		match lst_p_ev with
	| [] -> true
	| (p, b)::q -> try 
		let rep_find = Hashtbl.find h_ev_pst (ev.frm, p.name) in 
			if rep_find = 1 then verif_prestate q else false 
		with Not_found ->
			if verif_states b then (Hashtbl.add h_ev_pst (ev.next_frm,p.name) 1 ;verif_prestate q) 
			else (Hashtbl.add h_ev_pst (ev.next_frm,p.name) 0;remove_prestate p; false)
	in verif_prestate lst_prestate_succ
	
let rec verif_ev_non_imm_real lst_ev s  = match lst_ev with
| [] -> true
| ev::q -> let b_succ_ev = verif_succ ev s  in 
		if b_succ_ev then (Hashtbl.replace h_ev_st (ev.frm, s.name) 1; verif_ev_non_imm_real q s ) 
		else (Hashtbl.replace h_ev_st (ev.frm, s.name) 0;false)
	
let state_elimination ()  = 
  Hashtbl.clear h_ev_st;
	Hashtbl.clear h_ev_pst;
	Graph_tableau.iter_vertex (fun v -> 
		if (Graph_tableau.V.label v).category = V_State then (* This treatement is only for states *)
		 (
    		if Graph_tableau.mem_vertex tableau v then
    		let verif_vertex s = 
    			if is_complet_succ s then 
    				if verif_ev_non_imm_real (get_ev_non_imm_real s) s  then () else remove_state s
    			else
    				remove_state s
    		in verif_vertex v
			)
		else if (Graph_tableau.V.label v).category = V_Prestate then
			(
		   if Graph_tableau.mem_vertex tableau v && Graph_tableau.out_degree tableau v = 0 then
			 		remove_prestate v
			)
  ) tableau

let rec cycle_state_elimination lst_init_vertex   =
	 let card1 = Graph_tableau.nb_vertex tableau in
	  state_elimination ();
  let card2 = Graph_tableau.nb_vertex tableau in 
	let rep_open = is_open lst_init_vertex in 
  if card1 != card2 && rep_open
		then cycle_state_elimination lst_init_vertex
	  else rep_open
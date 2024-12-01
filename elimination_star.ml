open Except
open Modules
open Global

(* On conserve le vertex 0 pour connaître les états initiaux *)

(******************************************************************)
(*                        States Elimination                      *)
(******************************************************************)

 let is_complet_succ v = let ens_succ_mv =  
		Graph_tableau.fold_succ_e (fun e ens_mv ->
			let label_e = Graph_tableau.E.label e in Movecs.union ens_mv label_e
    ) tableau v Movecs.empty  
	 in Movecs.equal ens_succ_mv (Graph_tableau.V.label v).assoc_movecs

let simpl_andp phi1 phi2 = match (phi1,phi2) with
| State Top,State Top -> State Top
| State Top,psi | psi,State Top -> psi
| psi1,psi2 -> AndP (psi1,psi2) 
	
let simpl_orp phi1 phi2 = match (phi1,phi2) with
| State Top,_ | _, State Top -> State Top
| psi1,psi2 -> OrP (psi1,psi2) 
	
let whatfalse path ens_frm path_frm _st_name =
	let rec wf path_ev = match path_ev with
	| AndP(p1,p2) -> simpl_andp (wf p1) (wf p2)
	| OrP (p1,p2) -> simpl_orp (wf p1) (wf p2)
	| State(s) -> if State_Formulae.mem s ens_frm || Path_Formulae.mem path_ev path_frm
							  then State Top else path_ev
	| Next(_) -> State Top
	| Always(_) -> State Top
	| Until(_,State(s)) -> if State_Formulae.mem s ens_frm || Path_Formulae.mem (State s) path_frm
												 then State Top else path_ev
	| Until(_,p2) -> if Path_Formulae.mem p2 path_frm then State Top else path_ev
	| _ -> raise Impossible_case
	in wf path		  

let is_imm_real ev ens_frm st_name =
  let path = match ev.frm with 
	| Coal(_,p) | CoCoal(_,p) -> p 
	| _ -> raise Impossible_case  
	in let rep = whatfalse path ens_frm ev.path_frm st_name in 
	match rep with
	| State Top -> (true, State Top)
	| path -> (false, path)

let get_tuple frm lst_event = List.find (fun ev -> compare_formula ev.frm frm = 0) lst_event   
	
let get_ev_non_imm_real s = 
	List.fold_left (fun l ev -> 
		let (b,path) = is_imm_real ev s.ens_frm s.name in 
		if b then l else (ev,path)::l
	)[] s.event
	
	
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
| Coal (la,_) -> (try  fst (List.find (fun (_n,b) -> compare_formula b (Coal(la,Next (State next_ev))) = 0) lst_next_pos) 
							with Not_found ->	-2)
| CoCoal (la, _) when Agents.equal la !ag_all -> -1
| CoCoal (la,_) -> (try fst (List.find (fun (_n,b) -> compare_formula b (CoCoal(la,Next (State next_ev))) = 0) lst_next_neg)
								with Not_found -> -2)
| _ -> raise Impossible_case
	
		
let get_succ_prestates ev p = Graph_tableau.fold_succ (
		(* get all the states starting from a given prestate *)
		fun succ lst_s -> 
			(* Added 02/09/2015*)
			if Hashtbl.mem h_suppr succ.name then lst_s else
			(* End added *)
			let ev_next = get_tuple ev.next_frm (Graph_tableau.V.label succ).event in 
					 (succ,ev_next)::lst_s
		) tableau p []		
		
let get_succ_to_be_verified_simpl ev s = Graph_tableau.fold_succ_e ( (* go through all vectors from s *)
		fun edge l ->
	  	let num_ev = get_num_next_ev ev.next_frm (Graph_tableau.V.label s).lst_next_pos (Graph_tableau.V.label s).lst_next_neg in
			let l_edge = Graph_tableau.E.label edge and prestate = Graph_tableau.E.dst edge in
			(* Does the prestate correspond to the eventuality to be verified *) 
				if num_ev <> -2 &&  is_eventuality ev.next_frm && (State_Formulae.mem ev.next_frm (Graph_tableau.V.label prestate).ens_frm) && (verif_edge s l_edge ev num_ev) then
			    prestate::l
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
		(* Added 02/09/2015*)
		Graph_tableau.iter_succ_e ( 
      fun e -> Graph_tableau.remove_edge_e tableau e 
    ) tableau s ;
	  (* End added*) 
		(* Suppr 02/09/2015*)
		(* Graph_tableau.remove_vertex tableau s*)
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

let rec verif_succ ev st path = 
	let lst_prestate_succ = get_succ_to_be_verified_simpl ev st in 
	(* verification d'un état *)
	let rec verif_state (s, e) path =   
	let ens_frm = s.ens_frm in 
		match  whatfalse path ens_frm ev.path_frm s.name with
		| State Top -> true
		| path1 -> verif_succ e s path1
	and verif_prestate lst_prestate = match lst_prestate with
	| [] -> true
	| p::q -> 
		if Graph_tableau.out_degree tableau p = 0 then
			false 
		else
		try 
		(* If the prestate has already been studied, we need to check a new state *)
		let rep_find = (Hashtbl.find h_pst (p.name,path)) in
		 let rep_lst = rep_find.lst and rep_lst2 = rep_find.lst2 and rep_value = rep_find.value in 
			if rep_value = 1 then verif_prestate q else
		(if List.length rep_lst = 0 
			then (Hashtbl.replace h_pst (p.name,path) {value=2;lst=[];lst2=[]}; false)  else
			( Hashtbl.replace h_pst (p.name,path) {value=0;lst=(List.tl rep_lst);lst2=[]};
			let state_v = List.hd rep_lst and  tail = List.tl rep_lst in 
				   let sname = (fst state_v).name in 
				   try ignore (Hashtbl.find h_st (sname,path)) ;
							let new_list = List.tl rep_lst and new_tail = if List.length tail = 0 then [] else rep_lst2@[state_v] in
							(Hashtbl.replace h_pst (p.name,path) {value=0;lst=new_list;lst2=new_tail}; verif_prestate (p::q) ) 
				   with Not_found ->
						Hashtbl.add h_st (sname,path) 0;
      			if verif_state (List.hd rep_lst) path 
      			then (Hashtbl.replace h_pst (p.name,path) {value=1;lst=(List.tl rep_lst);lst2=rep_lst2}; verif_prestate q ) 
      			else verif_prestate lst_prestate
			)
			)
		with Not_found ->
	  (
			let lst_succ = get_succ_prestates ev p in 
			let state_v = List.hd lst_succ and  tail = List.tl lst_succ in 
				   let sname = (fst state_v).name in 
				   try ignore (Hashtbl.find h_st (sname,path)) ;
							let new_tail = if List.length tail = 0 then [] else [state_v] in
							Hashtbl.add h_pst (p.name,path)  {value=0;lst=(List.tl lst_succ);lst2=new_tail};
							verif_prestate (p::q)
						with Not_found -> 
							Hashtbl.add h_pst (p.name,path)  {value=0;lst=(List.tl lst_succ);lst2=[]};
								let b_succ = verif_state (List.hd lst_succ) path in
							if b_succ  
								then (Hashtbl.replace h_pst (p.name,path) {value=1;lst=(List.tl lst_succ);lst2=[]}; verif_prestate q ) 
								else verif_prestate lst_prestate
		)
	in verif_prestate lst_prestate_succ
	
let rec verif_ev_non_imm_real lst_ev s = match lst_ev with
| [] -> true
| (ev,path)::q ->  Hashtbl.clear h_pst; Hashtbl.clear h_st;
	  Hashtbl.add h_st (s.name,path) 0;
		let b_succ_ev = verif_succ ev s path  in 
		if b_succ_ev then  verif_ev_non_imm_real q s 
		else false
	
let state_elimination ()  = 
	
  Hashtbl.clear h_ev_st;
	Hashtbl.clear h_ev_pst;
	
	Graph_tableau.iter_vertex (fun v -> 
		if (Graph_tableau.V.label v).category = V_State then (* This treatement is only for states *)
		 (
    		if not(Hashtbl.mem h_suppr v.name) then
    		let verif_vertex s = 
    			if is_complet_succ s then 
(
    				if verif_ev_non_imm_real (get_ev_non_imm_real s) s  then () else remove_state s
)    			else
    				remove_state s
    		in verif_vertex v
			)
		else if (Graph_tableau.V.label v).category = V_Prestate then
			(
		   if (not(Hashtbl.mem h_suppr v.name)) && Graph_tableau.out_degree tableau v = 0 then
			 		remove_prestate v
			)
  ) tableau

let rec cycle_state_elimination lst_init_vertex   =
	(* suppr 02/09/2015*)
	(* 	let card1 = Graph_tableau.nb_vertex tableau in *)
	(* add 02/09/2015 (1 line) *)
	let card1 = Hashtbl.length h_suppr in 
	  state_elimination ();
	(* suppr 02/09/2015*)
	(*  let card2 = Graph_tableau.nb_vertex tableau in *)
	(* add 02/09/2015 (1 line) *)
	let card2 = Hashtbl.length h_suppr in 
	let rep_open = is_open lst_init_vertex in 
  if card1 != card2 && rep_open
		then cycle_state_elimination lst_init_vertex
	  else rep_open
open Modules
open Global
open Construction
open Elimination_star
open Pretty_printer

(* For states *)
(* return a new vertex if the set of formulae does not already exist or return the vertex corresponding to the set of formulae *) 
let get_or_create_state ens_formulae lst_event =
	(* new? :try ... with *)
	try 
		(Hashtbl.find h_states (string_of_formulae ens_formulae "line"), false)
	with Not_found ->  
		if is_inconsistant ens_formulae then
			(Graph_tableau.V.create { name ="" ; category = V_Empty ; ens_frm = State_Formulae.empty ; event = [] ;
				assoc_movecs = Movecs.empty ; lst_next_pos = [] ; lst_next_neg = [] ; lst_next_agents = []; nb_pos = -1 ; nb_neg = -1 },true)
		else
  		let (lst_nexttime_pos, lst_nexttime_neg, lst_nexttime_agents) = create_lst_nexttime ens_formulae in
  		let (nbr_pos,nbr_neg,nbr_agents) = (List.length lst_nexttime_pos, List.length lst_nexttime_neg, List.length lst_nexttime_agents) in
  		let vertex = if (nbr_pos + nbr_neg + nbr_agents) = 0 then
  			Graph_tableau.V.create {
  			name = generator_state false;
  		  category = V_State;
  		  ens_frm = State_Formulae.add (Coal(!ag_all, Next(State(Top)))) ens_formulae;
  			event = lst_event;
  		  assoc_movecs = create_lst_movecs 1;
  		  lst_next_pos = [ (0,Coal(!ag_all, Next(State(Top)))) ] ;
  	    lst_next_neg = [] ; 
				lst_next_agents = [];
  			nb_pos = 1;
  			nb_neg = nbr_neg;
  		}
  		else 
  			Graph_tableau.V.create {
  			name = generator_state false;
  		  category = V_State;
  		  ens_frm = ens_formulae;
  			event = lst_event;
  		  assoc_movecs = create_lst_movecs (max (nbr_pos + nbr_neg) 1);
  		  lst_next_pos = lst_nexttime_pos;
  			lst_next_neg = lst_nexttime_neg;
				lst_next_agents = lst_nexttime_agents;
  			nb_pos = nbr_pos;
  			nb_neg = nbr_neg
  		}	in 
      Hashtbl.add h_states (string_of_formulae ens_formulae "line") vertex ; (vertex,true)
			
(* For prestates *)
(* return a new vertex if the set of formulae does not already exist or return the vertex corresponding to the set of formulae *) 
let get_or_create_prestate ens_formulae lst_tuple= 
	(* new? : try ... with *)
	try
		(Hashtbl.find h_prestates (string_of_formulae ens_formulae "line"), false)
	with Not_found ->
		let vertex = Graph_tableau.V.create {
		   name = generator_pre_state false;
		   category = V_Prestate;
		   ens_frm = ens_formulae;
			 event = lst_tuple;
		   assoc_movecs = Movecs.empty;
		   lst_next_pos = [];
  		 lst_next_neg = [];
			 lst_next_agents = [];
  		 nb_pos = -1;
  		 nb_neg = -1;
		 } in 
		Hashtbl.add h_prestates (string_of_formulae ens_formulae "line") vertex ; (vertex, true) 
		
		
(* return a set of states to treat and the new hashtable for state, the tableau graph is updated *)		
let cons_from_pre lst_pre_todo  = 
   let rec cons_from lst_pre lst_new = match lst_pre with
   | [] -> lst_new
   | pre::q -> 
		 let label_pre = Graph_tableau.V.label pre in
       let rec treat_lst lst_ens_tuple lst_new = match lst_ens_tuple with
       | [] -> lst_new
       | ens_tuple::t -> 
					let rec get_detail ens_tuple =  
						Tuple_Formulae.fold 
							(fun tuple (e,l) -> if is_eventuality tuple.frm then 
																(State_Formulae.add tuple.frm e, tuple::l)
							              else 
																(State_Formulae.add tuple.frm e, l)
							) ens_tuple (State_Formulae.empty,[])
					in let (ens,lst_event) = get_detail ens_tuple
					in let treat_top ens = if State_Formulae.cardinal ens > 1 then State_Formulae.remove Top ens else ens
					in let (vertex, is_new) = get_or_create_state (treat_top ens) lst_event  
				  in
						Graph_tableau.add_edge tableau pre vertex;
	 						if not((Graph_tableau.V.label (vertex)).category = V_Empty) then 
								if is_new then treat_lst t (vertex::lst_new) else treat_lst t lst_new 
							else
								(Graph_tableau.remove_vertex tableau vertex; treat_lst t lst_new ) 
			in 
    		let lst_ens_tuple = Set_Tuple_Formulae.elements (rule_sr label_pre.ens_frm label_pre.event) in 
	  		let lst_n = treat_lst lst_ens_tuple lst_new in cons_from q lst_n
   in cons_from lst_pre_todo []  		
		
let cons_from_states lst_states_todo = 
   let rec cons_from lst_state lst_new = match lst_state with
     | [] -> lst_new
     | state::q -> 
			  let ls = Graph_tableau.V.label state in         (* for each state to be treated *)
        let rec treat_lst lst_ens_tuple lst_new = match lst_ens_tuple with    (* lst_ens is list of set of formulae *)
        | [] ->  lst_new
        | ((ens_frm,ens_mv),tuple_frm)::t -> 
					let lst_tuple = Tuple_Formulae.fold (
						fun tuple l -> if is_eventuality tuple.frm then	tuple::l else l
					) tuple_frm [] 
					in 
					  let (vertex, is_new) = get_or_create_prestate ens_frm lst_tuple in 
						Graph_tableau.add_edge_e tableau (Graph_tableau.E.create state ens_mv vertex); (* add a node and a labeled edge *)
            if is_new then treat_lst t (vertex::lst_new) else treat_lst t lst_new 
				in 
        let lst_ens_formulae_tuple = get_formulae_next_rule ls  in
        let lst_n = treat_lst lst_ens_formulae_tuple lst_new in cons_from q lst_n
    in cons_from lst_states_todo []       

let rec construct_state lst_pre_todo = 
  let lst_states_todo = cons_from_pre lst_pre_todo in 
    match lst_states_todo with
    | [] -> ()         (* the construction is finished, so we stop *)
    | lst -> construct_pre lst
and construct_pre lst_states_todo =
  let lst_pre_todo = cons_from_states lst_states_todo in 
    match lst_pre_todo with
    | [] -> ()         (* the construction is finished, so we stop *)
    | lst -> construct_state lst ;;

let get_eventualities_fst_pre set_frm =
	State_Formulae.fold ( 
			fun f lst ->
		 if Global.is_eventuality f then {frm=f; path_frm=Path_Formulae.empty; next_frm=Top; frm_origin=f}::lst else lst
		) set_frm [] 

(* return true if a formula is satisfiable and false otherwise *)
(* parse the formula, construct the tableau and the tableau of the formula to determine its satisfiability *)
let is_satisfiable set_frm media =
   (* Construction phase *)
   let vertex0 = Graph_tableau.V.create {
      name = "P0"; category = V_Prestate; ens_frm = set_frm; event=get_eventualities_fst_pre set_frm;
      assoc_movecs = Movecs.empty; lst_next_pos = [] ; lst_next_neg = [] ; lst_next_agents = [] ; nb_pos = -1 ;  nb_neg = -1 } in 
			Graph_tableau.add_vertex tableau vertex0;
   Hashtbl.add h_prestates (string_of_formulae set_frm "line") vertex0; 
	 ag_all := search_agents_in_set set_frm ;
   construct_state [vertex0]; 
	 (if media = "line" then print_endline "Fin de la construction du tableau"; print_endline (string_of_float (Sys.time() -. !time_start)));
	 let (nb_pst,nb_st) = Graph_tableau.fold_vertex (fun v (x,y) -> if v.category = V_Prestate then (x+1,y) else (x,y+1)) tableau (0,0) in
	 
	
	 if media = "web" then (print_endline "#I#"; print_graph tableau media ; statistic := !statistic ^ string_of_int nb_pst ^ ";" ^ string_of_int nb_st )
	    else 	(print_endline ("nb_prestate initial tableau: " ^  (string_of_int nb_pst) ^ "\nnb_state initial tableau:" ^ (string_of_int nb_st));
			let b = !verbatim in 
			if b then (
				  print_endline "*"; print_newline();
          print_endline "*";
          print_endline "* Initial Tableau";
          print_endline "*****************"; print_newline();
          print_graph tableau "line" )
				);
	  
		(*let frm = Pretty_printer.string_of_formulae (vertex0.ens_frm) "line" in
		Graphviz.graphviz_tableau "fichiers/tab_inter.gv" frm; *)
	
	
	(* Elimination phase *)
	(
		let lst_states_init = Graph_tableau.succ tableau vertex0 in
	  let result = cycle_state_elimination lst_states_init in 
		print_endline "Fin de la phase d'elimination"  ; print_endline (string_of_float (Sys.time() -. !time_start)); 
		(vertex0,result)
	)
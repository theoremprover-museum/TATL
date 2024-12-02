open Modules

let ag_all = ref Agents.empty;;
let contains_next = ref false;;
let statistic = ref "";;
let verbatim = ref false;;

let tableau = Graph_tableau.create();;
let model = Graph_model.create();;

let h_prestates = Hashtbl.create(500);;
let h_states = Hashtbl.create(500);; 
let h_ev_st = Hashtbl.create(500);;  (* (ev * state) : n where n = 0 if KO , n = 1 if OK, = 2 if undetermine *)
let h_ev_st_wf = Hashtbl.create(500);;
let h_ev_pst = Hashtbl.create(300);;  (* (ev * prestate) : n where n = 0 if KO , n = 1 if OK *)
let h_pst = Hashtbl.create(300);;  
let h_st = Hashtbl.create(300);; 
let h_prestate_default = Hashtbl.create(500);;
let h_level_state = Hashtbl.create(500);;
let h_suppr = Hashtbl.create(500);; 
let h_cluster = Hashtbl.create(200);;
let time_start = ref 0.0;;

(* initialisation des hashtables *)
let vertex = {
	name = ""; 
  category = V_Prestate ; 
  ens_frm = State_Formulae.empty ; 
	event = [];
	assoc_movecs = Movecs.empty ; 
	lst_next_pos = [];
	lst_next_neg = [];
	lst_next_agents = [];
	nb_pos = 0;
	nb_neg = 0;
} in 
let v = Graph_tableau.V.create vertex and
n = Graph_model.V.create 
{
	name_node = "";
	name_state = "";
	prop = State_Formulae.empty;	
} in
let l = {value=0;
         lst=[(vertex,{frm= Top; path_frm= Path_Formulae.empty;next_frm= Top; frm_origin=Top;})];
				 lst2=[(vertex,{frm= Top; path_frm= Path_Formulae.empty;next_frm= Top; frm_origin=Top;})];
        }
in Hashtbl.add h_prestates "" v; Hashtbl.clear h_prestates; 
   Hashtbl.add h_states "" v; Hashtbl.clear h_states;
   Hashtbl.add h_ev_pst (Prop "p", v.name) 0 ; Hashtbl.clear h_ev_pst;
   Hashtbl.add h_pst (v.name,State Top) l ; Hashtbl.clear h_pst;
   Hashtbl.add h_st (v.name,State Top) 0; Hashtbl.clear h_pst;
   Hashtbl.add h_ev_st (Prop "p", v.name) 0 ; Hashtbl.clear h_ev_st;
   Hashtbl.add h_ev_st_wf (Prop "p", v.name) Top ; Hashtbl.clear h_ev_st_wf;
   Hashtbl.add h_prestate_default v v; Hashtbl.clear h_prestate_default;
   Hashtbl.add h_suppr "" ""; Hashtbl.clear h_suppr;
   Hashtbl.add h_level_state (0, v.name) n ; Hashtbl.clear h_level_state;
   Hashtbl.add h_cluster n "" ; Hashtbl.clear h_cluster;;

(* reinitialisation function *)
let clear_all () = 
   Graph_tableau.clear tableau;  
   Graph_tableau.clear tableau;
   Hashtbl.clear h_prestates;
   Hashtbl.clear h_states;
   Hashtbl.clear h_ev_st;
   Hashtbl.clear h_suppr;
   Hashtbl.clear h_ev_pst;;
   
(* copy vertices and edges of tableau into tableau *)
(* vertices are added at the same time as edges *)
(*let copy_tableau_to_tableau () = 
 Graph_tableau.iter_edges_e (fun e -> Graph_tableau.add_edge_e tableau e) tableau;;  *)

(* counters *)
let counter_since n  = let increment = ref (n - 1) in fun r-> (if r then increment:=0 else incr increment); !increment ;;
let generator_state = let compt  = counter_since 1  in fun r -> "S" ^ string_of_int(compt r)
and generator_pre_state = let compt = counter_since 1  in fun r -> "P" ^ string_of_int(compt r)
and generator_node = let compt = counter_since 2  in fun r -> "n" ^ string_of_int(compt r)
and generator_cluster = let compt = counter_since 1 in fun r -> "C" ^ string_of_int(compt r);;

(* Get the set of agents included in a given formula. *)
let rec search_agent_state frm = 	match frm with
	| Top | Bot -> Agents.empty
	| Prop(_) | Neg(Prop(_)) -> Agents.empty
	| And(f1, f2) | Or(f1, f2) -> Agents.union (search_agent_state f1) (search_agent_state f2)
	| Coal(la, f) | CoCoal(la, f) -> Agents.union la (search_agent_path f)
	| _ -> raise Except.Impossible_case
and search_agent_path frm = match frm with
	| State f ->search_agent_state f
	| AndP(f1, f2) | OrP(f1, f2) -> Agents.union (search_agent_path f1) (search_agent_path f2)
	| Next f | Always f ->  search_agent_path f
	| Until(f1, f2) -> Agents.union (search_agent_path f1) (search_agent_path f2)
	| _ -> raise Except.Impossible_case
	
(* Get the set of agents included in a given set of formulae. *)
let search_agents_in_set set_frm =
	State_Formulae.fold 
	( fun frm set_agent -> Agents.union (search_agent_state frm) set_agent) set_frm Agents.empty 

(*return true is the formula is primitive and false otherwise *)
(* let is_primitive = function
	|	Top | Prop(_) | Neg(Prop(_))  -> true  (* case of literals *)
	| Coal(_,Next(State (_))) | CoCoal(_,Next(State (_))) -> true (* case of next formulae *)
	| _ -> false 
*)


	let rec contains_next_frm_state frm = match frm with
	| Top | Bot -> false
	| Prop _ -> false
	| Neg f -> contains_next_frm_state f 
	| And (f1,f2) -> contains_next_frm_state f1 || contains_next_frm_state f2
	| Or (f1,f2) -> contains_next_frm_state f1 || contains_next_frm_state f2
	| Coal (_,f) -> contains_next_frm_path f
	| CoCoal (_,f) -> contains_next_frm_path f
	| _ -> raise Except.Impossible_case
	and contains_next_frm_path frm = match frm with
	| State _ -> false
	| NegP f -> contains_next_frm_path f 
	| AndP (f1,f2) -> contains_next_frm_path f1 || contains_next_frm_path f2
	| OrP (f1,f2) -> contains_next_frm_path f1 || contains_next_frm_path f2
	| Next _ -> true
	| Always f -> contains_next_frm_path f 
	| Until (f1,f2) -> contains_next_frm_path f1 || contains_next_frm_path f2
  | _ -> raise Except.Impossible_case

let rec contains_eventuality_operator path = match path with
| State _ -> false
| Until (_,_) -> true
| AndP (f1,f2) | OrP (f1,f2) -> contains_eventuality_operator f1 || contains_eventuality_operator f2
| Next f | Always f ->  contains_eventuality_operator f
| _ -> raise Except.Impossible_case

(* return true if the formula is an eventuality and false otherwise *)
let is_eventuality frm =  match frm with 
| Coal (_,Next(_)) | CoCoal (_,Next(_)) -> false
| Coal (_,path) | CoCoal (_,path) -> contains_eventuality_operator path
| _ -> false

(* return true if the formula is a literal and false otherwise *)
let is_literal frm = match frm with
| Top | Bot | Prop _ | Neg (Prop _) -> true
| _ -> false

(* return true is the set of formulae is consistant and false otherwise *)
let is_inconsistant ens_frm =
	let ens_prop = State_Formulae.filter (fun f -> is_literal f) ens_frm in 
	if (State_Formulae.mem Top ens_prop) && (State_Formulae.mem Bot ens_prop) then true 
	else State_Formulae.exists (fun f -> State_Formulae.mem (Neg f) ens_prop) ens_prop
	
(* Added function: 02/09/2015 *)
(* return true is the set of formulae is consistant and false otherwise (for a set of tuples) *)
let is_inconsistant_tuple ens_tuple =
	let ens_prop_tuple = Tuple_Formulae.filter (fun f -> is_literal f.frm) ens_tuple in 
	let ens_prop = Tuple_Formulae.fold (fun f ens -> State_Formulae.add f.frm ens) ens_prop_tuple State_Formulae.empty in 
	if (State_Formulae.mem Top ens_prop) && (State_Formulae.mem Bot ens_prop) then true 
	else State_Formulae.exists (fun f -> State_Formulae.mem (Neg f) ens_prop) ens_prop

(* return true if  tableau is open and false otherwise *)
let rec is_open lst_state_init = match lst_state_init with
   | [] -> false
   | s::q -> 
		(* suppr 02/09/2015 *)
		(* if Graph_tableau.mem_vertex tableau s then true else is_open q *)
		(* add 02/09/2015 *)
		if Hashtbl.mem h_suppr s.name then is_open q else true

let rec pow c e = match e with
| 0 -> 1
| 1 -> c
| n -> let n1 = n-1 in c * (pow c n1)

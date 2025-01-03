open Global
open Modules
open Decomposition
	
(**********************************************************************************)
(**********************************************************************************)
(*                                 rule  SR                                       *)
(**********************************************************************************)
(**********************************************************************************)

let product set_ens1 set_ens2 =   (* return the product of the two set of sets *)
  if Set_Tuple_Formulae.cardinal set_ens1 = 0 then
		set_ens2 
	else if Set_Tuple_Formulae.cardinal set_ens2 = 0 then
		 set_ens1 
	else
	Set_Tuple_Formulae.fold (fun ens1 new_set1 ->
		let set1 = Set_Tuple_Formulae.fold (fun ens2 new_set2 -> 
		 Set_Tuple_Formulae.add (Tuple_Formulae.union ens1 ens2) new_set2  
		) set_ens2 Set_Tuple_Formulae.empty 
		in Set_Tuple_Formulae.union set1 new_set1 
	) set_ens1 Set_Tuple_Formulae.empty


(* return a set of set of formuale. Each one of the set of formulae will correspond *)
(* to a state in the pre-tableau *)
let rec saturation formula = match formula.frm with
| Top | Bot | Prop _ | Neg (Prop _) | Coal (_,Next(State _)) | CoCoal (_,Next(State _)) -> (* primitive *)
	Set_Tuple_Formulae.singleton (Tuple_Formulae.singleton {frm=formula.frm; path_frm = Path_Formulae.empty; next_frm=Top})        
(* cases of non-primitive formulae *)
| And (f1,f2) -> product (saturation {frm=f1;path_frm=Path_Formulae.empty;next_frm=Top}) (saturation {frm=f2;path_frm=Path_Formulae.empty;next_frm=Top})
| Or (f1,f2) -> Set_Tuple_Formulae.union (saturation {frm=f1;path_frm=Path_Formulae.empty;next_frm=Top}) (saturation {frm=f2;path_frm=Path_Formulae.empty;next_frm=Top})
| Coal(_la,_f1) | CoCoal (_la,_f1) -> 
	let set_gamma_comp = gamma_comp formula.frm in
  Tuple_Formulae.fold (
		fun t ens ->  Set_Tuple_Formulae.union (
			(* modif: 23/10/2015 //*)
			product 
				(Set_Tuple_Formulae.singleton (Tuple_Formulae.singleton {frm=formula.frm; path_frm=t.path_frm; next_frm=t.next_frm}))
				(saturation {frm=t.frm; path_frm=Path_Formulae.empty; next_frm=Top})
		) ens
	) set_gamma_comp Set_Tuple_Formulae.empty   
|_ -> raise Except.Impossible_case

(* Do the saturation for all formulae of the set ens_formulae to get the *)
(* result of the rule sr                                                 *)
let rule_sr ens_formulae =
 State_Formulae.fold (
	fun f ens ->   product (saturation {frm=f;path_frm=Path_Formulae.empty;next_frm=Top}) ens
 ) ens_formulae Set_Tuple_Formulae.empty

(**********************************************************************************)
(**********************************************************************************)
(*                                 rule  Next                                     *)
(**********************************************************************************)
(**********************************************************************************)

(* Determine two arrays, the first one for enforceable next-time formulae  *)
(* and the second on for unavoidable next-time formulae This formulae come *)
(* from a given set of state formulae                                      *)
let create_lst_nexttime ens_formulae = 
    let (ens1, ens2) = State_Formulae.partition (* Partition enforceable | unavoidable  *)
		( fun f -> match f with Coal (_, Next(State _)) -> true | _-> false ) 
		(State_Formulae.filter (* Partition enforceable and unavoidable next-time formulae | others*)
        (fun f -> match f with 
            | Coal (_, Next(State _)) | CoCoal (_, Next(State _)) -> true
            | _ -> false
        ) ens_formulae)
    in  let (ens3, ens2) = State_Formulae.partition (* Partition proper unavoidable | agents unavoidable *)
		( fun f -> match f with CoCoal (la, Next(State _)) when Agents.equal la !ag_all -> true | _ -> false) ens2
		in let (lst1,lst2) = ((State_Formulae.elements ens1),(State_Formulae.elements ens2)) 
		in (List.combine (Array.to_list(Array.init (List.length (lst1)) (fun i -> i))) lst1, (* list of numbered enforceable formulae *)
		    List.combine (Array.to_list(Array.init (List.length lst2) (fun i -> i))) lst2,
				State_Formulae.elements ens3) (* list of numbered unavoidable formulae *) 


(* return a matrix corresponding to all the move vectors we can obtain *)
(* for the set of agents ens_ag and the number nb.                     *)
let create_lst_movecs nb_next =
	let lst_agent = Agents.elements !ag_all in 
	let nb_agent = List.length lst_agent in  
	let borne = pow nb_next nb_agent in
	let matrix = Array.make_matrix borne nb_agent 0 in 
		for i = 0 to (nb_agent - 1) do
			let p = pow nb_next (nb_agent - i - 1) in  
			for j = 0 to borne - 1  do
				(matrix.(j).(i) <- (j / p) mod nb_next);
			done;
		done;
		(* transform the matrix into a set of move vectors via a list*)
		let lst = List.map (fun v -> List.combine lst_agent (Array.to_list v)) (Array.to_list matrix) in
		List.fold_left (fun ens_mv mv -> Movecs.add mv ens_mv ) Movecs.empty lst

(* Compute the function N(sigma) for a given move vector *)
let function_n_sigma movec nb_pos = 
  let lst_agent = fst( List.split(  (* to get the agent part of the move vector *)
		List.filter (fun m -> if (snd m) >= nb_pos then true else false) movec )) (* get the negative moves *)
  in List.fold_left (fun ens a -> Agents.add a ens) Agents.empty lst_agent
	
(* Compute the fonction Co(sigma) for a given move vector *)
let function_co_sigma movec nb_pos nb_neg = 
	let ens_agent = function_n_sigma movec nb_pos in 
	(Agents.fold (fun ag sum -> (List.assoc ag movec) - nb_pos + sum) ens_agent 0) mod nb_neg

(* compute the function Gamma(sigma) for a given move vector and a set of  *)
(* next-time formulae depending on the Gamma function                      *)
let function_gamma_sigma movec lst_next_enforc lst_next_unavoid lst_next_agents nb_pos nb_neg =
	let ens_st_form = List.fold_left ( fun ens nf -> match nf with     (* get the enforceable formulae *)
	 | (n,Coal(la,Next(State f))) -> if Agents.for_all (fun a -> (List.assoc a movec) == n) la 
				then State_Formulae.add f ens else ens
   | _ -> raise Except.Impossible_case
	) State_Formulae.empty lst_next_enforc 
	in let ens_st_form = List.fold_left ( fun ens nf -> match nf with  (* get the proper unavoidable formulae *)
		| (n,CoCoal(la,Next(State f))) ->
			if  (function_co_sigma movec nb_pos nb_neg) == n && 
		        Agents.subset (Agents.diff !ag_all la) (function_n_sigma movec nb_pos)		 
			then State_Formulae.add f ens else ens
		| _ -> raise Except.Impossible_case
	) ens_st_form lst_next_unavoid 
	in let ens_st_form = List.fold_left (fun ens nf -> match nf with
		| CoCoal (_, Next(State f)) -> State_Formulae.add f ens 
		| _ -> raise Except.Impossible_case
	) ens_st_form lst_next_agents
	in if State_Formulae.is_empty ens_st_form then State_Formulae.singleton Top else ens_st_form


(* Compute sets of formulae with the next procedure in order to obtain     *)
(* pre-state lately                                                        *)
let get_formulae_next_rule label =
	let (lst_next_enforc,lst_next_unavoid, lst_next_agents) = (label.lst_next_pos, label.lst_next_neg, label.lst_next_agents) in
  Movecs.fold (fun mv lst_frm_mv ->                     (* get the set of formulae attached to the move vector mv *)
		let ens_frm = function_gamma_sigma mv lst_next_enforc lst_next_unavoid lst_next_agents label.nb_pos label.nb_neg in
			let (l1,l2) = List.partition (fun (ens1, _) -> State_Formulae.equal ens1 ens_frm) lst_frm_mv (* check if there already exists such a set of formulae *)
			in match l1 with														                                              (* update l1 to get the new move vectors and let l2 unchanged *)
       | [] -> (ens_frm, Movecs.singleton mv)::l2
       | (ens_frm, ens_mv)::_q -> (ens_frm, Movecs.add mv ens_mv):: l2
		) label.assoc_movecs [] 
		
								
														
																				
																										
																																
																		            
                                                 
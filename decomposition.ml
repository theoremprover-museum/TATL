open Modules
open Global

(* hashtable use for the decomposition in order to avoid doing several times *)
(* the same computation                                                      *)
let h_decomp = Hashtbl.create(50);;
(* Initialisation de la hashtable *)
Hashtbl.add h_decomp "" Gamma_sets.empty 



let singl_top = Set_Path_Formulae.singleton (Path_Formulae.singleton (State Top))
let singl_path f = Set_Path_Formulae.singleton (Path_Formulae.singleton f)


(**********************************************************************************)
(**********************************************************************************)
(*                              Gamma-components                                  *)
(**********************************************************************************)
(**********************************************************************************)
let get_andP_formula_from ens = 
	  let ens = if Path_Formulae.cardinal ens > 1 then Path_Formulae.remove (State Top) ens else ens in 
    let lst_frm = Path_Formulae.elements ens in 
		let rec get_and_formulae lst = match lst with
		| [] -> raise Except.Impossible_case
		| [e] -> e
		| t::q -> AndP(t,get_and_formulae q)
	in get_and_formulae lst_frm


let get_and_formula_from ens = 
		 let ens = if State_Formulae.cardinal ens > 1 then State_Formulae.remove Top ens else ens in 
		let lst_frm = State_Formulae.elements ens in 
		let rec get_and lst = match lst with
		| [] -> raise Except.Impossible_case
		| [e] -> e
		| t::q -> And(t,get_and q)
	in get_and lst_frm
	
let get_orP_formulae_from ens = 
 if Path_Formulae.cardinal ens >= 1 && Path_Formulae.mem (State Top) ens  
 then	(State Top) 
 else 
 begin
		let lst_frm = Path_Formulae.elements ens in 
		let rec get_or lst = match lst with
		| [] -> raise Except.Impossible_case
		| [e] -> e
		| t::q -> OrP(t, get_or q)
	in get_or lst_frm 
 end


let get_and_OrP_formula_from ens = 
	 let ens = if Set_Path_Formulae.cardinal ens > 1 then Set_Path_Formulae.remove (Path_Formulae.singleton (State Top)) ens else ens in 
		let lst_frm = Set_Path_Formulae.elements ens in 
		let rec get_and lst = match lst with
		| [] -> raise Except.Impossible_case
		| [e] -> get_orP_formulae_from e
		| t::q -> AndP(get_orP_formulae_from t, get_and q)
	in get_and lst_frm 

(*Attention, on ne peut pas appliquer dans tous les cas *)
let simplification_1 t = 
	Set_Path_Formulae.fold (
		  fun ens_path new_set_ens -> let set_ens = Path_Formulae.fold (
					fun frm new_ens -> match frm with
					| Until (f1,State f2) -> if State_Formulae.mem f2 t.f1 then new_ens else Path_Formulae.add frm new_ens
					| _ -> Path_Formulae.add frm new_ens
				) ens_path Path_Formulae.empty in
				if Path_Formulae.cardinal set_ens = 0 then new_set_ens else	Set_Path_Formulae.add set_ens new_set_ens
		) t.f3 Set_Path_Formulae.empty
		
let simplification_2 set_ens_frm = 
	let (ens1, ens2) = Set_Path_Formulae.partition ( fun ens -> Path_Formulae.cardinal ens > 1	) set_ens_frm
	in Set_Path_Formulae.fold ( fun ens_path new_set_ens ->
		let res = Path_Formulae.fold ( fun frm b -> b || Set_Path_Formulae.mem (Path_Formulae.singleton frm) ens2 ) ens_path false
		in if res then Set_Path_Formulae.remove ens_path new_set_ens else new_set_ens
	) ens1 set_ens_frm
	
let simplification_tuple t = 
		let new_f3 = 
			let b = !contains_next in 
			if b then t.f3 else simplification_1 t
		in let new_f3_b =	if Set_Path_Formulae.is_empty new_f3 then singl_path (State Top) else new_f3
		in let res = simplification_2 new_f3_b in 
	{f1 = t.f1; f2 = t.f2 ;f3 =if  Set_Path_Formulae.is_empty res then singl_path (State Top) else res}
	

let otimes set1 set2 = 
    Gamma_sets.fold ( 
		  fun elt1 ens_1 -> let new_set = Gamma_sets.fold (
						fun elt2 ens_2 -> 
								Gamma_sets.add ( simplification_tuple {
							  f1 = State_Formulae.union elt1.f1 elt2.f1; 
								f2 = Path_Formulae.union elt1.f2 elt2.f2;
								f3 = if Set_Path_Formulae.equal elt1.f3 singl_top then elt2.f3
								     else if Set_Path_Formulae.equal elt2.f3 singl_top then elt1.f3 else Set_Path_Formulae.union elt1.f3 elt2.f3;
						}) ens_2
					) set2 Gamma_sets.empty in 
					Gamma_sets.union new_set ens_1
			) set1 Gamma_sets.empty

let produit_cart_ens set1 set2 = 
	Set_Path_Formulae.fold(
	fun elt1 ens_1 -> let new_set = Set_Path_Formulae.fold (
						fun elt2 ens_2 -> 
								Set_Path_Formulae.add (Path_Formulae.union elt1 elt2) ens_2
					) set2 Set_Path_Formulae.empty in 
					Set_Path_Formulae.union new_set ens_1
			) set1 Set_Path_Formulae.empty

let oplus set1 set2 = 
  Gamma_sets.fold ( 
		  fun elt1 ens_1 -> let new_set = Gamma_sets.fold (
						fun elt2 ens_2 -> if elt1.f3 <> singl_top && elt2.f3 <> singl_top then
							Gamma_sets.add (simplification_tuple {
							  f1 = State_Formulae.union elt1.f1 elt2.f1;
								f2 = Path_Formulae.union elt1.f2 elt2.f2;
								f3 = produit_cart_ens elt1.f3 elt2.f3;
							}) ens_2
							else ens_2
					) set2 Gamma_sets.empty in 
					Gamma_sets.union new_set ens_1
			) set1 Gamma_sets.empty
						
			
let rec gamma_sets path = 
(* on verifie si c'est dans la hashtable sinon on calcule et on ajoute     *)
(* dans la hastable                                                        *)
let str_path = Pretty_printer.string_of_path_line path in
try
	Hashtbl.find h_decomp str_path
with Not_found ->
begin
  	let decomp = match path with 
  | State f -> Gamma_sets.singleton { f1 = State_Formulae.singleton f; f2 = Path_Formulae.singleton path; f3 = singl_top }
  | Next f -> Gamma_sets.singleton { f1 = State_Formulae.singleton Top; f2 = Path_Formulae.singleton (State Top); f3 = singl_path f }
  | Always f -> begin match f with 
  		| State fs -> Gamma_sets.singleton { f1 = State_Formulae.singleton fs; f2 = Path_Formulae.singleton f ; f3 = singl_path (Always f) }
  		| fp -> otimes 
						(Gamma_sets.singleton { f1 = State_Formulae.singleton Top; f2 = Path_Formulae.singleton fp ; f3 = singl_path (Always f)})
						(gamma_sets fp)
  		end
  | Until (p1, p2) -> 
		let tuple1 = match p1 with
  		| State fs -> Gamma_sets.singleton { 
								f1 = State_Formulae.singleton fs; f2 = Path_Formulae.singleton p1 ; f3 = singl_path (Until (p1, p2)) }
  		| Always fp -> otimes
					  ( Gamma_sets.singleton { f1 = State_Formulae.singleton Top; f2 = Path_Formulae.singleton p1 ; f3 = Set_Path_Formulae.add (Path_Formulae.singleton p1) (singl_path  (Until (State Top, p2)))} )
						(gamma_sets p1)
			| Next (Always fp) -> Gamma_sets.singleton { f1 = State_Formulae.singleton Top ; f2= Path_Formulae.singleton p1 ; f3 = Set_Path_Formulae.add (Path_Formulae.singleton (Always fp)) (singl_path (Until (State Top, p2)))} 
			| fp -> otimes 
							(Gamma_sets.singleton { f1 = State_Formulae.singleton Top; f2 = Path_Formulae.singleton fp; f3 = singl_path (Until (p1, p2)) })
  		        (gamma_sets fp)
  	and tuple2 = match p2 with
  		| State fs -> Gamma_sets.singleton { f1 = State_Formulae.singleton fs; f2 = Path_Formulae.singleton p2 ; f3 = singl_path (State Top) }
  		| fp -> otimes 
					(Gamma_sets.singleton { f1 = State_Formulae.singleton Top; f2 = Path_Formulae.singleton fp; f3 = singl_path (State Top) })
					(gamma_sets fp) 
		in Gamma_sets.union tuple1 tuple2
	| AndP (p1,p2) ->  otimes (gamma_sets p1) (gamma_sets p2)
  | OrP (p1, p2) ->  let g1 = gamma_sets p1 and g2 = gamma_sets p2 in 
				Gamma_sets.union g1 (Gamma_sets.union g2 (oplus g1 g2)) 
  | _ -> raise Except.Impossible_case
  in Hashtbl.add h_decomp str_path decomp; decomp
end



(* return the gamma-components of a gamma-formula *)
let gamma_comp formula = 
	contains_next:= contains_next_frm_state formula;  
	match formula with
| Coal(la,f) -> let set_tuple = gamma_sets f in 
  Gamma_sets.fold (fun t ens -> 
		let ens_f1 = t.f1 and ens_f2 = t.f2 and f3 = get_and_OrP_formula_from t.f3 in  (* Attention suppression du clear_setAnd ici *)
		let f1 = get_and_formula_from ens_f1 in 
  	let form = match f3 with
  		| State Top -> f1
  		| _ ->	And(f1,Coal(la,Next(State(Coal(la,f3))))) 
  	in Tuple_Formulae.add {frm =form; path_frm = ens_f2 ; next_frm=Coal(la,f3)}  ens
  ) set_tuple Tuple_Formulae.empty 
| CoCoal(la,f) ->  let set_tuple = gamma_sets f in 
  Gamma_sets.fold (fun t ens -> 
		let ens_f1 = t.f1 and ens_f2 = t.f2 and f3 = get_and_OrP_formula_from t.f3 in  (* Attention suppression du clear_setAnd ici *)
		let f1 = get_and_formula_from ens_f1 in 
		let form = match f3 with
  		| State Top -> f1
  		| _ ->	And(f1,CoCoal(la,Next(State(CoCoal(la,f3))))) 
  	in Tuple_Formulae.add {frm =form; path_frm = ens_f2; next_frm=CoCoal(la,f3)}  ens
  ) set_tuple Tuple_Formulae.empty 
| _ -> raise Except.Impossible_case 
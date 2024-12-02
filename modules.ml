open Graph;;

(*--------------------------------------------*)
(*-----            Agents                -----*)
(*--------------------------------------------*)

module Agents = Set.Make(
	struct
		type t = int
		let compare = compare
	end);;

(*--------------------------------------------*)
(*-----     Vecteurs de mouvements       -----*)
(*--------------------------------------------*)
module Movecs = Set.Make(
	struct
		type t = (int * int) list  (* (num_agent * num_mov) list *)
		let compare = compare
	end);;

module Movecs_bool = Set.Make(
  struct
     type t = (Movecs.t * bool)
     let compare = compare
  end);;


(*--------------------------------------------*)
(*-----           Formules               -----*)
(*--------------------------------------------*)



type state_formula =
	| Top | Bot 
	| Prop of string
	| Neg of state_formula
	| And of state_formula * state_formula
	| Or of state_formula * state_formula
	| Imply of state_formula * state_formula
	| Equiv of state_formula * state_formula
	| Coal of Agents.t * path_formula
	| CoCoal of Agents.t * path_formula
and path_formula =
	| State of state_formula
	| NegP of path_formula
	| AndP of path_formula * path_formula
	| OrP of path_formula * path_formula
	| ImplyP of path_formula * path_formula
	| EquivP of path_formula * path_formula
	| Next of path_formula
	| Always of path_formula
	| Until of path_formula * path_formula
	| Release of path_formula * path_formula
	| Event of path_formula

(* Sorting of state formulae : Top, Prop, Enforceable next-time formulae, unavoidable next-time formulae, all the others *)
let compare_formula f1 f2 = match (f1,f2) with
| Top,Top -> 0
| Top, _ -> -1
| _, Top -> 1
| Prop _, Prop _ -> compare f1 f2 
| Prop _, _ -> -1
| _ , Prop _ -> 1
| Coal (_,Next(State(_))), Coal (_,Next(State(_))) -> compare f1 f2 (* enforcable next-time formulae *)
| Coal (_,Next(State(_))), _ -> -1
| _, Coal (_,Next(State(_))) -> 1
| CoCoal (_,Next(State(_))), CoCoal (_,Next(State(_))) -> compare f1 f2 (* unavoidable next-time formulae *)
| CoCoal (_,Next(State(_))), _ -> -1
| _, CoCoal (_,Next(State(_))) -> 1
| _ -> compare f1 f2
	
type cat_reali = NONE | TRUE | FALSE | MAYBE


module State_Formulae = Set.Make(  (* set of state formulae *)
	struct
		type t = state_formula		
		let compare = compare_formula
	end);;

module Path_Formulae = Set.Make(   (* set of path formulae *)
	struct
		type t = path_formula
		let compare = compare
  end);;

module Set_State_Formulae = Set.Make(  
	struct
		type t = State_Formulae.t
		let compare = State_Formulae.compare
	end);;

module Set_Path_Formulae = Set.Make(  
	struct
		type t = Path_Formulae.t
		let compare = Path_Formulae.compare
	end);;

type formula_tuple = {
		frm: state_formula;
		path_frm: Path_Formulae.t;
		next_frm: state_formula;
		frm_origin: state_formula;	
	}
			
let compare_tuple t1 t2 = compare_formula t1.frm t2.frm

module Tuple_Formulae = Set.Make(
	struct
		type t = formula_tuple
		let compare = compare_tuple
	end);;

module Set_Tuple_Formulae = Set.Make(  
	struct
		type t = Tuple_Formulae.t
		let compare = Tuple_Formulae.compare
	end);;


type gamma_tuple = {
		f1 : State_Formulae.t;  (* state_formula for the present state *)
		f2 : Path_Formulae.t;   (* path_formula for the present state *)
 		f3 : Set_Path_Formulae.t;   (* Set of Set of path_formulae for the next state And/Or Set*)
	}


module Gamma_sets = Set.Make(
	 struct
		type t = gamma_tuple
		let compare = compare
	end);;



(*--------------------------------------------*)
(*-----             Etats                -----*)
(*--------------------------------------------*)
type categ = V_State | V_Prestate | V_Empty

type vertex = {
	 name : string ;
	 category : categ ;
	 ens_frm : State_Formulae.t ;
	 event: (formula_tuple) list;
	 assoc_movecs : Movecs.t ;
	 lst_next_pos : (int * state_formula) list;
	 lst_next_neg : (int * state_formula) list;
	 lst_next_agents: state_formula list;
	 nb_pos : int;
	 nb_neg : int; 
}	 


type edge = {
	 vector : Movecs.t;
	 event_e: State_Formulae.t;
 	}
	
module V = struct
  type t = vertex
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;

module E = struct
  type t = edge
  let compare = compare
  let equal = (=)
  let default = {vector=Movecs.empty; event_e=State_Formulae.empty}
end;;

module Graph_tableau = Imperative.Digraph.ConcreteLabeled(V)(E);;

type node =   {
	 name_node : string;
	 name_state : string;
	 prop : State_Formulae.t
	}

module N = struct
  type t = node
  let compare = compare
  let hash = Hashtbl.hash
  let equal = (=)
end;;

module Graph_model = Imperative.Digraph.ConcreteLabeled(N)(E);;

type lst_state = {
	value: int;
	lst : (vertex*formula_tuple )list;
	lst2: (vertex*formula_tuple )list;
	}
	

(*--------------------------------------------*)
(*-----             CLUSTERS             -----*)
(*--------------------------------------------*)

(* un cluster est un ensemble d'états. On souhaite partitionner *)
(* les modèles en cluster pour appliquer l'algorithme de Kanellakis *)
(* et Smolka revisité *)


module Cluster = Set.Make (
	struct
		type t = node
		let compare = compare
	end);;
	
type cluster = {
	nom : string;
	element : Cluster.t
}

module Set_Nom_Cluster = Set.Make (
	struct 
		type t = string
		let compare = compare
    end);;
	
module Partition = Set.Make (
	struct
		type t = cluster
		let compare = compare
	end);;
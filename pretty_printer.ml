open Modules
open Transformation_frm

(* ----------------------------------------------------------- *)
(* ----                       General                     ---- *)
(* ----------------------------------------------------------- *)

(* Convert a boolean into a representative string *)
let string_of_bool_inconst b = match b with
		true -> "Inconsistant"
	| false -> "Consistant"

(* ----------------------------------------------------------- *)
(* ----            Pour  les agents                       ---- *)
(* ----------------------------------------------------------- *)

let string_of_agents ens_agents media =
	let lst_agents = Agents.elements ens_agents in
	let rec string_of lst = match lst with
			[] ->  if media = "web" then "&amp;empty;" else ""
		| [x] -> string_of_int x
		| x:: q -> (string_of_int x) ^ "," ^ (string_of q)
	in string_of lst_agents;;

let string_of_agents_brut ens_agents =
	let lst_agents = Agents.elements ens_agents in
	let rec string_of lst = match lst with
			[] -> ""
		| [x] -> string_of_int x
		| x:: q -> (string_of_int x) ^ ";" ^ (string_of q)
	in string_of lst_agents;;

let string_of_agents_line ens_agents =
	let lst_agents = Agents.elements ens_agents in
	let rec string_of lst = match lst with
			[] -> ""
		| [x] -> string_of_int x
		| x:: q -> (string_of_int x) ^ "," ^ (string_of q)
	in string_of lst_agents;;

(* ----------------------------------------------------------- *)
(* ----            Pour les vecteurs de mouvements        ---- *)
(* ----------------------------------------------------------- *)

(* Transform a set of movecs into a string. Precise the media where to     *)
(* display.                           *)
let rec string_of_movec vector media = match vector with
	| [] -> if media = "web" then "&amp;empty;" else ""
	| [(a,m)] -> string_of_int m
	| (a,m)::q -> (string_of_int m) ^ "," ^ (string_of_movec q media)
	
	
let string_of_movecs ens_movecs media=
	let lst_movecs = Movecs.elements ens_movecs  in
	let rec string_of lst = match lst with
		| [] -> ""
		| [t] -> "("^(string_of_movec t media) ^ ")"
		| t:: q -> "("^(string_of_movec t media) ^ ")" ^ (string_of q)
	in string_of lst_movecs


let is_or frm = match frm with
| Or (_,_) -> true
| _-> false

let is_and frm = match frm with 
| And(_,_) -> true
| _ -> false

let is_and_or_until path = match path with
| Until (State Top,_) -> false
| AndP (_,_) | OrP (_,_) | Until (_,_) -> true
| _ -> false

let is_and_until path = match path with
| Until (State Top,_) -> false
| AndP (_,_) | Until(_,_) -> true
| _ -> false

let is_or_until path = match path with
| Until (State Top,_) -> false
| OrP (_,_) | Until(_,_) -> true
| _ -> false

(* ----------------------------------------------------------- *)
(* ----                Pour une formule   (ligne)         ---- *)
(* ----------------------------------------------------------- *)
let dlangle = "<<" and drangle = ">>" and 
		dlcrochet = "[[" and drcrochet = "]]"
		
let rec string_of_state_line frm =	match frm with
		| Top -> "T"
		| Bot -> "&" (*à trouver*)
		| Prop str -> str
		| Neg (Prop str) -> "~" ^ str 
		| And(phi1, phi2) -> 
				let part1 = if is_or phi1 then "(" ^ (string_of_state_line phi1) ^ ")" 
					else string_of_state_line phi1 
				and part2 =  if is_or phi2 then "(" ^ (string_of_state_line phi2) ^ ")" 
					else string_of_state_line phi2
				in part1 ^ " /\\ " ^ part2
		| Or(phi1, phi2) -> 
				let part1 = if is_and phi1 then "(" ^ (string_of_state_line phi1) ^ ")" 
					else string_of_state_line phi1 
				and part2 =  if is_and phi2 then "(" ^ (string_of_state_line phi2) ^ ")" 
					else string_of_state_line phi2
				in part1 ^ " \\/ " ^ part2
		| Coal (la, phi) -> dlangle ^ (string_of_agents la "line") ^ drangle ^ 
				(if is_and_or_until phi then "(" ^ (string_of_path_line phi) ^ ")" 
					else string_of_path_line phi )
		| CoCoal (la,phi) -> dlcrochet ^ (string_of_agents la "line") ^ drcrochet ^ 
				(if is_and_or_until phi then "(" ^ (string_of_path_line phi) ^ ")" 
					else string_of_path_line phi )
		|_ -> raise	Except.Impossible_case
	and string_of_path_line frm =  match frm with
		| State phi ->  string_of_state_line phi 
		| AndP(phi1, phi2) -> 
				let part1 = if is_or_until phi1 then "(" ^ (string_of_path_line phi1) ^ ")" 
					else string_of_path_line phi1 
				and part2 =  if is_or_until phi2 then "(" ^ (string_of_path_line phi2) ^ ")" 
					else string_of_path_line phi2
				in part1 ^ " /\\ " ^ part2
		| OrP(phi1, phi2) -> 
				let part1 = if is_and_until phi1 then "(" ^ (string_of_path_line phi1) ^ ")" 
					else string_of_path_line phi1 
				and part2 =  if is_and_until phi2 then "(" ^ (string_of_path_line phi2) ^ ")" 
					else string_of_path_line phi2
				in part1 ^ " \\/ " ^ part2
		| Next(phi) -> "X" ^ if is_and_or_until phi then "(" ^ (string_of_path_line phi) ^ ")" 
					else string_of_path_line phi 
		| Always(phi) -> "G" ^ if is_and_or_until phi then  "(" ^ (string_of_path_line phi) ^ ")" 
					 else 
					(
						let toto = phi in
						string_of_path_line toto 
					)
		| Event(phi) -> "F" ^ if is_and_or_until phi then "(" ^ (string_of_path_line phi) ^ ")" 
					else string_of_path_line phi 
		| Until (State Top, phi) -> string_of_path_line (Event phi)
		| Until(State(Prop str), phi) -> str ^ "U" ^ 
					if is_and_or_until phi then "(" ^ (string_of_path_line phi) ^ ")" 
					else string_of_path_line phi 
		| Until(State(Neg(Prop str)), phi) -> "~" ^ str ^ "U" ^ 
					if is_and_or_until phi then "(" ^ (string_of_path_line phi) ^ ")" 
					else string_of_path_line phi 
		| Until(phi1, phi2) -> "(" ^ (string_of_path_line phi1) ^ ")U" ^ 
				  if is_and_or_until phi2 then "(" ^ (string_of_path_line phi2) ^ ")" 
					else string_of_path_line phi2 
		|_ -> raise	Except.Impossible_case

(* ----------------------------------------------------------- *)
(* ----                Pour une formule   (web  )         ---- *)
(* ----------------------------------------------------------- *)
let dlangle_w = "&amp;lt;&amp;lt;" and drangle_w = "&amp;gt&amp;gt;" and 
		dlcrochet_w = "[[" and drcrochet_w = "]]" and neg="~" 
		
let rec string_of_state_web frm =	match frm with
		| Top -> "T"
		| Bot -> "#" (*à trouver*)
		| Prop str -> str
		| Neg (Prop str) -> neg ^ str
		| And(phi1, phi2) -> 
				let part1 = if is_or phi1 then "(" ^ (string_of_state_web phi1) ^ ")" 
					else string_of_state_web phi1 
				and part2 =  if is_or phi2 then "(" ^ (string_of_state_web phi2) ^ ")" 
					else string_of_state_web phi2
				in part1 ^ " /\\ " ^ part2
		| Or(phi1, phi2) -> 
				let part1 = if is_and phi1 then "(" ^ (string_of_state_web phi1) ^ ")" 
					else string_of_state_web phi1 
				and part2 =  if is_and phi2 then "(" ^ (string_of_state_web phi2) ^ ")" 
					else string_of_state_web phi2
				in part1 ^ " \\/ " ^ part2
		| Coal (la, phi) ->  dlangle_w ^ (string_of_agents la "web") ^ drangle_w ^ 
				(if is_and_or_until phi then "(" ^ (string_of_path_web phi) ^ ")" 
					else string_of_path_web phi )
		| CoCoal (la,phi) -> dlcrochet_w ^ (string_of_agents la "web") ^ drcrochet_w ^ 
				(if is_and_or_until phi then "(" ^ (string_of_path_web phi) ^ ")" 
					else string_of_path_web phi )
		| _ -> raise Except.Impossible_case
	and string_of_path_web frm = match frm with
		| State phi ->  string_of_state_web phi 
		| AndP(phi1, phi2) -> 
			let part1 = if is_or_until phi1 then "(" ^ (string_of_path_web phi1) ^ ")" 
					else string_of_path_web phi1 
				and part2 =  if is_or_until phi2 then "(" ^ (string_of_path_web phi2) ^ ")" 
					else string_of_path_web phi2
				in part1 ^ " /\\ " ^ part2
		| OrP(phi1, phi2) -> 
			let part1 = if is_and_until phi1 then "(" ^ (string_of_path_web phi1) ^ ")" 
					else string_of_path_web phi1 
				and part2 =  if is_and_until phi2 then "(" ^ (string_of_path_web phi2) ^ ")" 
					else string_of_path_web phi2
				in part1 ^ " \\/ " ^ part2
		| Next(phi) -> "X" ^ if is_and_or_until phi then "(" ^ (string_of_path_web phi) ^ ")" 
					else string_of_path_web phi 
		| Always(phi) -> "G" ^ if is_and_or_until phi then "(" ^ (string_of_path_web phi) ^ ")" 
					else string_of_path_web phi 
		| Event(phi) -> "F" ^ if is_and_or_until phi then "(" ^ (string_of_path_web phi) ^ ")" 
					else string_of_path_web phi 
		| Until (State Top, phi) -> string_of_path_web (Event phi)
		| Until(State(Prop str), phi) -> str ^ "U" ^ 
					if is_and_or_until phi then "(" ^ (string_of_path_web phi) ^ ")" 
					else string_of_path_web phi 
		| Until(State(Neg(Prop str)), phi) -> "~" ^ str ^ "U" ^ 
					if is_and_or_until phi then "(" ^ (string_of_path_web phi) ^ ")" 
					else string_of_path_web phi 
		| Until(phi1, phi2) -> "(" ^ (string_of_path_web phi1) ^ ")U" ^ 
				  if is_and_or_until phi2 then "(" ^ (string_of_path_web phi2) ^ ")" 
					else string_of_path_web phi2 			
		| _ -> raise Except.Impossible_case
		
(* Transform a formula into a string in order to be used in the printing   *)
(* of data on the web                                                      *)
let string_of_formula frm media = 
	if media = "web" then string_of_state_web (transform_shortcut_state frm)
	else string_of_state_line (transform_shortcut_state frm) 



(* ----------------------------------------------------------- *)
(* ----        Pour un ensemble de formules               ---- *)
(* ----------------------------------------------------------- *)

(* Transform a set of formulae into a string in order to be used in the printing of data on the web *)
let string_of_formulae ens_formulae media = 
  let lst_formulae = State_Formulae.elements ens_formulae in 
	let rec string_of lst = match lst with
	| [] -> ""
	| [x] -> string_of_formula x media
	| t::q -> (string_of_formula t media)^" ; "^(string_of q)
	in string_of lst_formulae

(* Transform a set of path formulae into a string in order to be used in the printing of data on command line *)
let string_of_path_formulae ens_formulae = 
  let lst_formulae = Path_Formulae.elements ens_formulae in 
	let rec string_of lst = match lst with
	| [] -> ""
	| [x] -> string_of_path_line x
	| t::q -> (string_of_path_line t)^" ; "^(string_of q)
	in string_of lst_formulae

let string_of_lst_tuples tuples = 
	let rec string_of lst = match lst with
	| [] -> ""
	| [x] -> (string_of_formula x.frm "line") ^ "<:>" ^ (string_of_path_formulae x.path_frm) ^ "<:>" ^ 
	(string_of_formula x.next_frm "line") ^ "<:>" ^ (string_of_formula x.frm_origin "line");
	| t::q -> (string_of_formula t.frm "line") ^ "<:>" ^ (string_of_path_formulae t.path_frm) ^ "<:>" ^ 
	(string_of_formula t.next_frm "line") ^ "<:>" ^ (string_of_formula t.frm_origin "line") ^ " ; " ^ (string_of q)
	in string_of tuples


let string_of_tuples set_tuples = 
	let tuples = Tuple_Formulae.elements set_tuples in 
	string_of_lst_tuples tuples

let string_of_set_tuple set_tuple = 
	let lst_tuples = Set_Tuple_Formulae.elements set_tuple in 
	let rec string_of lst = match lst with
	| [] -> ""
	| [x] -> "{" ^ (string_of_tuples x) ^ "}" 
	| t::q -> "{" ^ (string_of_tuples t) ^ "}" ^ " ; " ^ (string_of q)
	in string_of lst_tuples 

(* ----------------------------------------------------------- *)
(* ----        Pour un ensemble d'états                   ---- *)
(* ----------------------------------------------------------- *) 

(* Transform a state into a string in order to be used in the printing of  *)
(* data on the web                                                         *)
let string_of_state state media = 
	if media = "web" then  "#N#" ^  state.name ^ "\n#F#" ^ (string_of_formulae state.ens_frm "web")^"\n"
	else  state.name ^ " : " ^ (string_of_formulae state.ens_frm "line") ^"\n" ^ 
	      "[debug] liste eventualites: " ^ (string_of_lst_tuples state.event) ^ "\n"
	
(* get all the vertexes and sort them *)
let sort_vertex_graph graph =
  let lst =  Graph_tableau.fold_vertex (
     fun v l -> (* add 02/09/2015 (1 line) *)
			if Hashtbl.mem Global.h_suppr v.name then l else 
				((Graph_tableau.V.label v).name,v)::l
  ) graph [] in 
  List.sort (
    fun (n1,v1) (n2,v2) -> let (part1a, part1b) = (Str.string_before n1 1, Str.string_after n1 1) 
                           and (part2a, part2b) = (Str.string_before n2 1, Str.string_after n2 1) in
	if (part1a < part2a) || (part1a = part2a && ((int_of_string part1b) < (int_of_string part2b))) 
        then -1	else 1 
  ) lst

(* imprime le graphe à l'écran ou sur la sortie web *)
let print_graph graph media = 
  let sorted_lst = sort_vertex_graph graph in  
  List.iter (
   fun (_,v) -> let data_vertex = Graph_tableau.V.label v  and cpt = ref 0 in 
   if media = "web" then 
	print_string (string_of_state data_vertex "web" ^ "#S#")
   else                                                      
	print_string (string_of_state data_vertex "line" ^ " Succ: ") 
  ;
      Graph_tableau.iter_succ (
	  fun s -> 
			(* add 02/09/2015 (1 line) *)
			if not(Hashtbl.mem Global.h_suppr s.name) then 
			let edge = Graph_tableau.find_edge graph v s 
	           and name_s = (Graph_tableau.V.label s).name in
	  if !cpt = 0 then incr cpt else print_string " ; " ; 
	     if data_vertex.category == V_State then
	         print_string ((string_of_movecs (Graph_tableau.E.label edge) media) ^ "->" ^ name_s)
	     else
		 print_string name_s
     ) graph v;
     print_endline("\n");
 ) sorted_lst

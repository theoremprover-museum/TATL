open Modules
open Global

(* Initialisation de la partition initiale qui contient tous les noeuds du modèle *)
let cluster_init () =  
	let c_init = Graph_model.fold_vertex ( fun n c -> Cluster.add c n ) model Cluster.empty in 
	Graph.model.iter_vertex (fun n -> Hashtbl.add h_cluster n "C0") model ; c_init

(**       Fonctions pour la fonction equivalence **)

(* comparaison des ensembles de propositions positives de deux noeuds*)
(* !!! Cette fonction sera peut-être à supprimer si on ne garde que les  *)
(* propositions positives dans les noeuds du modèle. !!! *)
let compare_node_prop n1 n2 = 
	let filtre s = State_formulae.filter (
	fun e -> match e with Prop _ -> true | _ -> false ) s in 
	let prop_n1 = filter n1.prop
	and prop_n2 = filter n2.prop in 
	State_formulae.compare prop_n1 prop_n2
	
(* Récupère tous les clusters atteints depuis un noeud donné      *)
(* avec n'importe quel vecteur pour tous les agents :             *)
(* pour tous les joueurs, je n'ai pas besoin de tester plus que ça*)	
let succ_cluster n = 
	Graph_model.fold_succ (
		fun s e ->  let c = hashtabl.find h_cluster s in 
			Set_Nom_Cluster.add e c 
	) model Set_Nom_Cluster.empty
	
	
let get_movecs_clusters n =
    Graph_model.fold_edges_e (
		fun e l -> let s = Graph_model.E.dst e in 
				let c = hashtbl.find h_cluster s in 
				(e.vector, c)::l 
	) model []	
	
(* permet de vérifier si des ensembles de clusters sont inclus dans *)
(* d'autres ensembles de cluster *)	
let rec is_superset_sub c v i = 
	if i < Array.length v then
		if Set_Nom_Cluster.subset v.(i) c then
			true
		else is_superset_sub c v (i + 1)
	else
		false
	done

let rec is_superset v1 v2 i  = 
	if i < Array.length v1 then
		if is_superset_sub v1.(i) v2 0 then
			is_superset v1 v2 (i+1)
		else	
			false
	else true
	
(* donne la liste de toutes les partitions *)	
let rec rajoute lst x = match lst with
| [] -> [[x]];
| h::t -> (x::h)::rajoute t x

let rec get_coalitions agents = match agents with
| [] -> [];
| x::t -> let sans_x = parties t in
 let avec_x = rajoute sans_x x in
 sans_x@avec_x	
	
let equivalence_by_coalition nb_act_s nb_act_t cpl_s cpl_t =  (* coal est une liste *)
	let lst_agents = Agents.elements ag_all in 
	let lst_coalitions = get_coalitions lst_agents in 
	let rec equiv_coalition lst_coal = match lst_coal with
		| [] -> true
		| coal::q -> 
		let v_s = Array.create nb_act_s Set_Nom_Cluster.empty
		and v_t = Array.create nb_act_t Set_Nom_Cluster.empty in
		(* Remplir les vecteurs *)
		List.iter (fun (mv,c) -> 
			List.iter (fun (a, m) -> if List.mem a coal then v_s.(m) <- Set_Nom_Cluster.add v_s.(m) c ) mv
		) cplt_mov_clus_s;
		List.iter (fun (mv,c) -> 
			List.iter (fun (a, m) -> if List.mem a coal then v_t.(m) <- Set_Nom_Cluster.add v_t.(m) c ) mv
		) cplt_mov_clus_t;
		(* Il faut maintenant comparer les deux tableaux *)
		if is_superset v_s v_t 0 then 
		   if is_superset v_t v_s 1 then
				equiv_coalition q
		   else false
		else false
	in equiv_coalition lst_coalitions
	
	
(* s et t sont deux noeuds. partition correspond à un ensemble de clusters *)	
let equivalence s t =
 if s = t then true
 else
 if compare_node_prop s t = 0 then (* les deux noeuds ont les mêmes propositions positives *)
	if Set_cluster.compare (succ_cluster s) (succ_cluster t) = 0 then
		let equivalent = ref true ;
		let nb_act_s = s.nb_pos + s.nb_neg and nb_act_t = t.nb_pos + t.nb_neg in 
		let cple_mov_clus_s = get_movecs_clusters s and cple_mov_clus_t = get_movecs_clusters t in 
		equivalence_by_coalition b_act_s nb_act_t cple_mov_clus_s cple_mov_clus_t
	else false
 else false
 
 (**               Fonction Split             *)
 
 let split B =    (* B est un cluster, renvoie une liste d'au plus deux clusters *)
	let s = Cluster.choose B in
	let (b1,b2) = Cluster.fold ( 
		fun t (bloc1,bloc2) -> if equivalence s t then Cluster.add bloc1 t else Cluster.add bloc2 t)
	) B (Cluster.empty(),Cluster.empty())
	in if cluster.is_empty then [b1] else [b1;b2]
	
(** 				Algorithme Kanellakis et Smolka modifié                     **)

let rec refinement partition = 
	let rec refin lst_part change new_partition = match lst_part with
	| [] -> (change,new_partition)
	| c::q -> let lst_split = split c in 
		if List.length lst_split = 2 then
			let (b1,lst_b2) = (List.hd lst_split, List.tl lst_split) in 
			let b2 = List.hd lst_b2 in 
			(* mise à jour de la hash table *)	
			let c1 = generator_cluster () and c2 = generator_cluster () in
			Cluster.iter (fun n -> Hashtbl.remove h_cluster n; Hashtbl.add h_cluster n c1) b1;
			Cluster.iter (fun n -> Hashtbl.remove h_cluster n; Hashtbl.add h_cluster n c2) b2;
			refin (b1::b2::q) true new_partition
		else	
			refin q change c::new_partition
	in 		
		let (change, new_partition) = refin partition false [] in 
		if change then refinement new_partition
		else new_partition
		
let start_refinement () = 
	refinement [cluster_init()]
	
	
 
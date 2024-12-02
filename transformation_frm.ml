open Modules

(* AD -- 28/08/2014 *)

let rec transform_fnn_state frm = match frm with 
	| Top | Bot |  Prop _ -> frm
	| Neg (Neg f) -> transform_fnn_state f
	| Neg Top -> Bot
	| Neg Bot -> Top
	| Neg(And (f1,f2)) -> Or (transform_fnn_state (Neg f1), transform_fnn_state (Neg f2))
	| Neg(Or (f1,f2)) -> And (transform_fnn_state (Neg f1), transform_fnn_state (Neg f2))
	| Neg(Imply(f1,f2)) -> And (transform_fnn_state f1, transform_fnn_state (Neg f2))
	| Neg(Equiv (f1,f2)) -> And (transform_fnn_state (Or (f1,f2)), transform_fnn_state (Or (Neg f1,Neg f2)))
	| Neg(Coal(la,f)) -> CoCoal (la, transform_fnn_path (NegP f))
	| Neg(CoCoal(la,f)) -> Coal (la, transform_fnn_path (NegP f))
	| Neg f -> Neg (transform_fnn_state f)														(* Il faudra revoir toute la suite*)
	| And (f1,f2) -> let f1 = And (transform_fnn_state f1, transform_fnn_state f2) in f1
	| Or (f1,f2) -> Or (transform_fnn_state f1, transform_fnn_state f2)
	| Imply (f1,f2) -> Or (transform_fnn_state (Neg f1), transform_fnn_state f2)
	| Equiv (f1,f2) -> Or (transform_fnn_state (And (f1,f2)), transform_fnn_state (And (Neg f1,Neg f2)))
	| Coal (la,f2) -> Coal (la, transform_fnn_path f2)
	| CoCoal (la,f2) -> CoCoal (la, transform_fnn_path f2)
and transform_fnn_path frm = match frm with
	| State f -> State (transform_fnn_state f)
	| NegP (NegP f) -> transform_fnn_path f
	| NegP (Next f) -> Next (transform_fnn_path (NegP f))
	| NegP (State f) -> State (transform_fnn_state (Neg f))
	| NegP (Until (State Top, f)) -> Always(transform_fnn_path (NegP f))
	| NegP (Until (f1,f2)) -> let f1_t = transform_fnn_path (NegP f1) and f2_t = transform_fnn_path (NegP f2) in 
						OrP(Always f2_t,Until(f2_t,AndP (f1_t,f2_t)))
	| NegP (Always f) -> Until(State(Top), transform_fnn_path(NegP f))
	| NegP (Event f) -> Always(transform_fnn_path(NegP f))
	| NegP(AndP (f1,f2)) -> OrP (transform_fnn_path (NegP f1), transform_fnn_path (NegP f2))
	| NegP(OrP (f1,f2)) -> AndP (transform_fnn_path (NegP f1), transform_fnn_path (NegP f2))
	| NegP(ImplyP (f1,f2)) -> AndP (transform_fnn_path f1, transform_fnn_path (NegP f2))
	| NegP(EquivP (f1,f2)) -> AndP (transform_fnn_path (OrP (f1,f2)), transform_fnn_path (OrP (NegP f1,NegP f2)))
	| NegP f -> NegP (transform_fnn_path f) 
	| AndP (f1,f2) -> AndP (transform_fnn_path f1, transform_fnn_path f2) 
	| OrP  (f1,f2) -> OrP (transform_fnn_path f1, transform_fnn_path f2) 
	| ImplyP (f1,f2) -> OrP (transform_fnn_path (NegP f1), transform_fnn_path f2) 
	| EquivP (f1,f2) -> OrP (transform_fnn_path (AndP (f1,f2)), transform_fnn_path (AndP (NegP f1,NegP f2)))
	| Next f -> Next (transform_fnn_path f)
	| Always f -> Always (transform_fnn_path f)
	| Until (f1,f2) -> Until (transform_fnn_path f1, transform_fnn_path f2) 
	| Release (f1,f2) -> let f1_t = transform_fnn_path (NegP f1) and f2_t = transform_fnn_path (NegP f2) in 
						OrP (Always f1_t , Until (f1_t, AndP(f1_t,f2_t))) 
	| Event f -> Until(State Top, transform_fnn_path f)

let transform_fnn frm = 
	let new_frm = transform_fnn_state frm in 
	if compare_formula frm new_frm = 0 then new_frm else transform_fnn_state new_frm

let rec simplification_state frm = match frm with 
	| Top | Bot |  Prop _ -> frm
	| Neg (Coal (la, f)) -> CoCoal(la,(simplification_path (NegP f)))
	| Neg (Neg f) -> simplification_state f
	| Neg Top -> Bot
	| Neg Bot -> Top
	| And (f1,f2) -> let f1 = And (simplification_state f1, simplification_state f2) in f1
	| Or (f1,f2) -> Or (simplification_state f1, simplification_state f2)
	| Coal (la,f2) -> Coal (la, simplification_path f2)
	| CoCoal (la,f2) -> CoCoal (la, simplification_path f2)
	| _ -> raise Except.Impossible_case
and simplification_path frm = match frm with
	| State f -> State (simplification_state f)
	| NegP f -> NegP (simplification_path f) 
	| AndP (f1,f2) -> AndP (simplification_path f1, simplification_path f2) 
	| OrP  (f1,f2) -> OrP (simplification_path f1, simplification_path f2) 
	| Next f -> Next (simplification_path f)
	| Always (Always f) -> (simplification_path (Always f))
	| Always (Next f) -> Next(simplification_path (Always f))
	| Always (Until (State Top, (Always f))) -> simplification_path (Until (State Top , Always f))
	| Always f -> Always (simplification_path f)
	| Until (State Top, Always(Until (State Top,f))) -> simplification_path (Always (Until (State Top, f)))  (* Event Always Event f *)
	| Until (State Top, Until (State Top, f)) -> simplification_path (Until (State Top, f))  (* Event Event f*)
	| Until (State Top, Until (_, f)) -> simplification_path (Until (State Top, f))
	| Until (_,Until (State Top, f)) -> simplification_path (Event f)
	| Until (f1,f2) -> Until (simplification_path f1, simplification_path f2) 
  | _ -> raise Except.Impossible_case

let rec simplification frm = 
	let new_frm = simplification_state frm in 
	if compare_formula frm new_frm = 0 then new_frm else simplification new_frm

  let rec transform_shortcut_state frm = match frm with
	| Top | Bot |  Prop _ -> frm
	| Neg f -> Neg(transform_shortcut_state f)													(* Il faudra revoir toute la suite*)
	| And (f1,f2) -> And (transform_shortcut_state f1, transform_shortcut_state f2)
	| Or (f1,f2) -> Or (transform_shortcut_state f1, transform_shortcut_state f2)
	| Imply (f1,f2) -> Imply (transform_shortcut_state f1, transform_shortcut_state f2)
	| Equiv (f1,f2) -> Equiv (transform_shortcut_state f1, transform_shortcut_state f2)
	| Coal (la,f2) -> Coal (la, transform_shortcut_path f2)
	| CoCoal (la,f2) -> CoCoal (la, transform_shortcut_path f2)
and transform_shortcut_path frm = match frm with
	| State f -> State (transform_shortcut_state f)
	| NegP f -> NegP (transform_shortcut_path f) 
	| AndP (f1,f2) -> AndP (transform_shortcut_path f1, transform_shortcut_path f2) 
	| OrP  (f1,f2) -> OrP (transform_shortcut_path f1, transform_shortcut_path f2) 
	| ImplyP (f1,f2) -> ImplyP (transform_shortcut_path f1, transform_shortcut_path f2) 
	| EquivP (f1,f2) -> EquivP (transform_shortcut_path f1, transform_shortcut_path f2) 
	| Next f -> Next (transform_shortcut_path f)
	| Always f -> Always (transform_shortcut_path f)
	| Until (State(Top),f) -> Event (transform_shortcut_path f)
	| Until (f1,f2) -> Until (transform_shortcut_path f1, transform_shortcut_path f2) 
	| Release (f1,f2) -> Release (transform_shortcut_path f1, transform_shortcut_path f2) 
	| Event f ->  transform_shortcut_path f
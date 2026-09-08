(* Proof grammars (Sect. 3).

   A production is [p(V_1,..,V_n) -> d]. A grammar is an ordered list of
   productions with pairwise different nonterminals such that a nonterminal only
   refers to earlier ones (the i < j invariant). *)

type production = {
  name : string;        (* nonterminal p *)
  arity : int;          (* n = number of parameters V_1..V_n *)
  rhs : Term.t;         (* d *)
}

type t = production list

(* Substitute parameters V_i in a proof term by [args.(i-1)]. *)
let rec subst_params (t : Term.t) (args : Term.t array) : Term.t =
  match t.Term.node with
  | Term.Param i ->
    if i >= 1 && i <= Array.length args then args.(i - 1)
    else t
  | Term.App (name, ts) ->
    Term.app name (Array.map (fun x -> subst_params x args) ts)

let find (g : t) (name : string) : production option =
  List.find_opt (fun p -> String.equal p.name name) g

let table (g : t) : (string, production) Hashtbl.t =
  let h = Hashtbl.create (2 * List.length g + 1) in
  List.iter (fun p -> Hashtbl.replace h p.name p) g;
  h

(* val_G : exhaustively expand a term using the grammar's productions
   (Sect. 3). This materialises the full tree; it is only meant for small
   terms, as the expanded proofs of set.mm are gigantic (O6). *)
let value (g : t) (t0 : Term.t) : Term.t =
  let tbl = table g in
  let rec go (t : Term.t) : Term.t =
    match t.Term.node with
    | Term.Param _ -> t
    | Term.App (name, args) -> (
      let args' = Array.map go args in
      match Hashtbl.find_opt tbl name with
      | Some prod -> go (subst_params prod.rhs args')
      | None -> Term.app name args')
  in
  go t0

(* |p| = size of the production = size of its RHS. *)
let production_size (p : production) : int = Term.size p.rhs

(* |G| = sum of production sizes. *)
let size (g : t) : int = List.fold_left (fun acc p -> acc + production_size p) 0 g

(* N(G) = number of productions = number of PDNet nodes. *)
let num_productions (g : t) : int = List.length g

(* Number of occurrences of the symbol [name] in [t]. *)
let occurrences_in (t : Term.t) (name : string) : int =
  let rec go t acc =
    match t.Term.node with
    | Term.Param _ -> acc
    | Term.App (n, args) ->
      let acc = if String.equal n name then acc + 1 else acc in
      Array.fold_left (fun a c -> go c a) acc args
  in
  go t 0

(* ref_G(p): number of occurrences of nonterminal [name] across all RHSs
   (in-degree in the PDNet). *)
let ref_count (g : t) (name : string) : int =
  List.fold_left (fun acc p -> acc + occurrences_in p.rhs name) 0 g

(* Element i-1 = number of occurrences of V_i in the RHS, for i = 1..arity. *)
let param_occurrences (p : production) : int array =
  let occ = Array.make p.arity 0 in
  let rec go t =
    match t.Term.node with
    | Term.Param i -> if i >= 1 && i <= p.arity then occ.(i - 1) <- occ.(i - 1) + 1
    | Term.App (_, args) -> Array.iter go args
  in
  go p.rhs;
  occ

(* A production is linear if no parameter occurs more than once in its RHS. *)
let is_linear (p : production) : bool =
  Array.for_all (fun c -> c <= 1) (param_occurrences p)

(* Replace every application of nonterminal [name]/[arity] in [t] by its
   definition [def] with the parameters substituted (an unfolding step). *)
let unfold_in (t : Term.t) (name : string) (arity : int) (def : Term.t) : Term.t =
  let rec go t =
    match t.Term.node with
    | Term.Param _ -> t
    | Term.App (n, args) ->
      let args = Array.map go args in
      if String.equal n name && Array.length args = arity then subst_params def args
      else Term.app n args
  in
  go t

(* G' of Sect. 4: [g] with [p]'s production removed and unfolded in all
   remaining RHSs. *)
let unfold_production (g : t) (p : production) : t =
  List.filter_map
    (fun q ->
      if String.equal q.name p.name then None
      else Some { q with rhs = unfold_in q.rhs p.name p.arity p.rhs })
    g

(* sav_G(p) (Sect. 4): |G'| - |G|, where G' is G after removing p's
   production and unfolding it in all RHSs. The paper's closed form

     ref_G(p) * (|d| - arity(p)) - |d|

   holds only when every parameter of p occurs exactly once in d (a linear
   production without LHS-only parameters); it is used as a fast path in that
   case. About a third of the productions of set.mm are nonlinear, so the
   general definition matters. *)
let save_value (g : t) (p : production) : int =
  if Array.for_all (fun c -> c = 1) (param_occurrences p) then
    (ref_count g p.name * (production_size p - p.arity)) - production_size p
  else size (unfold_production g p) - size g

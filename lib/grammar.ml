(* Proof grammars and knowledge bases (Sect. 3, Defs. 7, 8).

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

let is_nonterminal (g : t) (name : string) : bool =
  List.exists (fun p -> String.equal p.name name) g

(* val_G : exhaustively expand a term using the grammar's productions
   (Sect. 3). WARNING: this materialises the full tree and is only meant for
   small terms; the whole point of the engine is to avoid calling it on the
   gigantic proofs. *)
let rec value (g : t) (t0 : Term.t) : Term.t =
  match t0.Term.node with
  | Term.Param _ -> t0
  | Term.App (name, args) -> (
    let args' = Array.map (value g) args in
    match find g name with
    | Some prod -> value g (subst_params prod.rhs args')
    | None -> Term.app name args')

(* |p| = size of the production = size of its RHS (Sect. 3). *)
let production_size (p : production) : int = Term.size p.rhs

(* |G| = sum of production sizes. *)
let size (g : t) : int = List.fold_left (fun acc p -> acc + production_size p) 0 g

(* Number of productions = number of PDNet nodes. *)
let num_productions (g : t) : int = List.length g

(* ref_G(p): number of occurrences of nonterminal [name] across all RHSs
   (in-degree in the PDNet). *)
let occurrences_in (t : Term.t) (name : string) : int =
  let rec go t acc =
    match t.Term.node with
    | Term.Param _ -> acc
    | Term.App (n, args) ->
      let acc = if String.equal n name then acc + 1 else acc in
      Array.fold_left (fun a c -> go c a) acc args
  in
  go t 0

let ref_count (g : t) (name : string) : int =
  List.fold_left (fun acc p -> acc + occurrences_in p.rhs name) 0 g

(* sav_G(p) for a linear production (Sect. 4, line 151):
     ref_G(p) * (|d| - arity(p)) - |d|.
   The grammar-size reduction contributed by the production. *)
let save_value (g : t) (p : production) : int =
  let r = ref_count g p.name in
  (r * (production_size p - p.arity)) - production_size p

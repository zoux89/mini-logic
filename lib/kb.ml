(* Knowledge bases, grammar-MGT and shallow-MGT (Sect. 3, Defs. 7, 8).

   A KB is a triple <B, F, G>:
   - [base]      : presupposition base B (axioms / terminals),
   - [formulas]  : the stated theorem clauses F_i, by nonterminal name,
   - [grammar]   : the proof grammar G (one production per theorem).

   Def. 8 requires F_i >=. shallow-mgt_K(p_i) for every production. *)

type t = {
  base : Cddc.base;
  formulas : (string, Formula.clause) Hashtbl.t;
  grammar : Grammar.t;
}

exception Undefined

(* Compute mgt_{B'}(d_i) for each production in order, where B' is the base
   enriched by [enrich] with the results for earlier productions. Raises
   [Undefined] as soon as one MGT is undefined. *)
let successive (base : Cddc.base) (g : Grammar.t)
    ~(enrich : Cddc.base -> Grammar.production -> Formula.clause -> unit) :
    (string, Formula.clause) Hashtbl.t =
  let b' = Hashtbl.copy base in
  let out = Hashtbl.create 256 in
  List.iter
    (fun p ->
      match Cddc.mgt_k b' p.Grammar.rhs p.Grammar.arity with
      | Some c ->
        Hashtbl.replace out p.Grammar.name c;
        enrich b' p c
      | None -> raise Undefined)
    g;
  out

(* grammar-mgt (Def. 7): the MGT of each production's RHS, computed against a
   base successively enriched with the grammar-MGTs of earlier productions.
   If any involved MGT is undefined, the grammar-MGT is undefined for all
   productions and [None] is returned. *)
let grammar_mgts (base : Cddc.base) (g : Grammar.t) :
    (string, Formula.clause) Hashtbl.t option =
  try
    Some
      (successive base g ~enrich:(fun b' p c ->
           Hashtbl.replace b' p.Grammar.name c))
  with Undefined -> None

(* shallow-mgt (Def. 8): like grammar-mgt but the base is enriched with the
   *stated* formulas F_j of earlier productions rather than their computed
   MGTs. [None] if some F_j is missing or some MGT is undefined. *)
let shallow_mgts (k : t) : (string, Formula.clause) Hashtbl.t option =
  try
    Some
      (successive k.base k.grammar ~enrich:(fun b' p _ ->
           match Hashtbl.find_opt k.formulas p.Grammar.name with
           | Some f -> Hashtbl.replace b' p.Grammar.name f
           | None -> raise Undefined))
  with Undefined -> None

(* Def. 8 side condition: every stated F_i is an instance of shallow-mgt(p_i). *)
let is_kb (k : t) : bool =
  match shallow_mgts k with
  | None -> false
  | Some sh ->
    List.for_all
      (fun p ->
        match Hashtbl.find_opt k.formulas p.Grammar.name,
              Hashtbl.find_opt sh p.Grammar.name with
        | Some f, Some m -> Formula.instance_of f m
        | _ -> false)
      k.grammar

(* Names whose stated F_i is a *strict* instance of its shallow-MGT
   (Table 2, column ">. mgt"; observation O8), in grammar order. *)
let strict_instances (k : t) : string list =
  match shallow_mgts k with
  | None -> []
  | Some sh ->
    List.filter_map
      (fun p ->
        match Hashtbl.find_opt k.formulas p.Grammar.name,
              Hashtbl.find_opt sh p.Grammar.name with
        | Some f, Some m when Formula.strict_instance_of f m -> Some p.Grammar.name
        | _ -> None)
      k.grammar

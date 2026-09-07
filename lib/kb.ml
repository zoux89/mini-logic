(* Knowledge bases and the grammar-MGT / shallow-MGT (Sect. 3, Defs. 7, 8).

   A KB is a triple <B, F, G>:
   - [base]      : presupposition base B (axioms),
   - [formulas]  : the stated theorem clauses F (as found in the source, e.g.
                   set.mm), one per production, by nonterminal name,
   - [grammar]   : the proof grammar G (one production per theorem). *)

type t = {
  base : Cddc.base;
  formulas : (string, Formula.clause) Hashtbl.t;
  grammar : Grammar.t;
}

(* grammar-mgt (Def. 7): the MGT of each production's RHS, computed against a
   base successively enriched with the grammar-MGTs of earlier productions.
   Returns a table name -> clause; a name is absent if its grammar-MGT is
   undefined. *)
let grammar_mgts (base : Cddc.base) (g : Grammar.t) :
    (string, Formula.clause) Hashtbl.t =
  let b' = Hashtbl.copy base in
  let out = Hashtbl.create 256 in
  List.iter
    (fun p ->
      match Cddc.mgt_k b' p.Grammar.rhs p.Grammar.arity with
      | Some c ->
        Hashtbl.replace out p.Grammar.name c;
        Hashtbl.replace b' p.Grammar.name c
      | None -> ())
    g;
  out

(* shallow-mgt (Def. 8): like grammar-mgt but the base is enriched with the
   *stated* formulas F_j of earlier productions rather than their computed MGTs.
   Used to check F_i >= shallow-mgt(p_i) and to detect strict instances (O8). *)
let shallow_mgts (k : t) : (string, Formula.clause) Hashtbl.t =
  let b' = Hashtbl.copy k.base in
  let out = Hashtbl.create 256 in
  List.iter
    (fun p ->
      (match Cddc.mgt_k b' p.Grammar.rhs p.Grammar.arity with
       | Some c -> Hashtbl.replace out p.Grammar.name c
       | None -> ());
      match Hashtbl.find_opt k.formulas p.Grammar.name with
      | Some f -> Hashtbl.replace b' p.Grammar.name f
      | None -> ())
    k.grammar;
  out

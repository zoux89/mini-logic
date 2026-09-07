(* The CDDC inference system: computing the Most General Theorem of a proof
   term (Sect. 2, Table 1, Def. 2).

   A presupposition base maps a name [p] to its clause [A <- B_1 /\ ... /\ B_n];
   arity(p) = n.

   [mgt base d] computes mgt_base(d) (Def. 2), returning [None] when undefined.

   Algorithm (a direct reading of rules App / Par / Ins):
   - Allocate fresh variables u_1..u_k, one per parameter V_i (rule Par makes
     the conclusion of an occurrence of V_i be exactly u_i).
   - Recurse on the term. For [App (p, [d_1;..;d_n])], take a fresh copy of p's
     clause [A <- B_1 /\ .. /\ B_n], recursively compute the conclusion c_i of
     each d_i, and unify B_i with c_i (rule App). The conclusion is A.
   - Because the u_i are shared variables, constraints from every occurrence of
     a parameter are merged through unification -- this is exactly the merging
     of {U, R_1, .., R_n} in rule App, and it is what makes nonlinear proof
     terms possibly yield a strict instance or an undefined MGT (Prop. 4). *)

type base = (string, Formula.clause) Hashtbl.t

let base_of_list (l : (string * Formula.clause) list) : base =
  let b = Hashtbl.create 64 in
  List.iter (fun (n, c) -> Hashtbl.replace b n c) l;
  b

let arity_of (b : base) (name : string) : int option =
  match Hashtbl.find_opt b name with
  | Some c -> Some (List.length c.Formula.body)
  | None -> None

exception Undefined

let mgt_k (b : base) (d : Term.t) (k : int) : Formula.clause option =
  let s = Formula.create_subst () in
  (* us.(i) is u_{i} for i in 1..k; index 0 unused. *)
  let us = Array.init (k + 1) (fun _ -> Formula.fresh ()) in
  let rec go (d : Term.t) : Formula.fterm =
    match d.Term.node with
    | Term.Param i ->
      if i < 1 || i > k then raise Undefined else us.(i)
    | Term.App (name, args) -> (
      match Hashtbl.find_opt b name with
      | None -> raise Undefined
      | Some cl ->
        let n = List.length cl.Formula.body in
        if Array.length args <> n then raise Undefined;
        let cl = Formula.rename_clause cl in
        List.iteri
          (fun idx bpi ->
            let ci = go args.(idx) in
            if not (Formula.unify s bpi ci) then raise Undefined)
          cl.Formula.body;
        cl.Formula.head)
  in
  try
    let concl = go d in
    let head = Formula.apply s concl in
    let body =
      Array.to_list (Array.init k (fun i -> Formula.apply s us.(i + 1)))
    in
    Some { Formula.head; body }
  with Undefined -> None

(* Convenience: infer k from the largest parameter index in [d]. *)
let mgt (b : base) (d : Term.t) : Formula.clause option =
  mgt_k b d (Term.max_param d)

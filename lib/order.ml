(* Ordering and pruning of proof grammars.

   [topo] reorders productions so that a nonterminal is defined before it is
   used (the paper's i < j invariant, Sect. 3): referenced productions come
   first, top-level ones last.

   [prune] is TreeRePair's pruning phase (Sect. 5, line 183): productions whose
   save-value is <= 0 are eliminated by unfolding them in all RHSs. Top-level
   productions (those with no references, e.g. Start / stated theorems) are
   protected from elimination. *)

let topo (g : Grammar.t) : Grammar.t =
  let byname = Hashtbl.create 64 in
  List.iter (fun p -> Hashtbl.replace byname p.Grammar.name p) g;
  let visited = Hashtbl.create 64 and temp = Hashtbl.create 64 in
  let out = ref [] in
  let rec visit name =
    if Hashtbl.mem visited name || Hashtbl.mem temp name then ()
    else
      match Hashtbl.find_opt byname name with
      | None -> () (* terminal *)
      | Some p ->
        Hashtbl.replace temp name ();
        let rec refs t =
          match t.Term.node with
          | Term.Param _ -> ()
          | Term.App (n, args) ->
            if Hashtbl.mem byname n then visit n;
            Array.iter refs args
        in
        refs p.Grammar.rhs;
        Hashtbl.remove temp name;
        Hashtbl.replace visited name ();
        out := p :: !out
  in
  List.iter (fun p -> visit p.Grammar.name) g;
  List.rev !out

(* Replace every application of nonterminal [name]/[arity] in [t] by its
   definition [def] with the parameters substituted (an unfolding step). *)
let unfold_in (t : Term.t) (name : string) (arity : int) (def : Term.t) : Term.t =
  let rec go t =
    match t.Term.node with
    | Term.Param _ -> t
    | Term.App (n, args) ->
      let args = Array.map go args in
      if String.equal n name && Array.length args = arity then
        Grammar.subst_params def args
      else Term.app n args
  in
  go t

let prune ?protect (g : Grammar.t) : Grammar.t =
  let g = ref g in
  let protect_name n =
    match protect with Some f -> f n | None -> false
  in
  let is_protected p =
    protect_name p.Grammar.name || Grammar.ref_count !g p.Grammar.name = 0
  in
  let continue = ref true in
  while !continue do
    continue := false;
    match
      List.find_opt
        (fun p -> (not (is_protected p)) && Grammar.save_value !g p <= 0)
        !g
    with
    | None -> ()
    | Some p ->
      continue := true;
      let nm = p.Grammar.name and ar = p.Grammar.arity and def = p.Grammar.rhs in
      g :=
        List.filter_map
          (fun q ->
            if String.equal q.Grammar.name nm then None
            else Some { q with Grammar.rhs = unfold_in q.Grammar.rhs nm ar def })
          !g
  done;
  !g

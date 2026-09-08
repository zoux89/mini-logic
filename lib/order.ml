(* Ordering and pruning of proof grammars.

   [topo] reorders productions so that a nonterminal is defined before it is
   used (the paper's i < j invariant, Sect. 3): referenced productions come
   first, top-level ones last.

   [prune] is TreeRePair's pruning phase (Sect. 5): productions whose
   save-value is <= 0 are eliminated by unfolding them in all RHSs. Top-level
   productions (those with no references, e.g. Start / stated theorems) and
   those selected by [protect] are never eliminated. *)

let topo (g : Grammar.t) : Grammar.t =
  let byname = Grammar.table g in
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

let prune ?(protect = fun _ -> false) (g : Grammar.t) : Grammar.t =
  let g = ref g in
  let is_protected p =
    protect p.Grammar.name || Grammar.ref_count !g p.Grammar.name = 0
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
      g := Grammar.unfold_production !g p
  done;
  !g

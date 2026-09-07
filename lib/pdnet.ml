(* Proof Dependency Network (Def. 9, Sect. 4-5).

   PDNet(G) is the directed graph whose nodes are the nonterminals of G and
   whose edges p -> q represent an occurrence of q in the RHS of p's production
   ("q is a direct premise of p"). ref_G(q) is the in-degree of q. *)

type t = {
  nodes : string list;
  (* edges with multiplicity: (p, q, count) *)
  edges : (string * string * int) list;
}

let of_grammar (g : Grammar.t) : t =
  let nodes = List.map (fun p -> p.Grammar.name) g in
  let nodeset = Hashtbl.create 256 in
  List.iter (fun n -> Hashtbl.replace nodeset n ()) nodes;
  let edges =
    List.concat_map
      (fun p ->
        (* count occurrences of each nonterminal q in p's RHS *)
        let counts = Hashtbl.create 16 in
        let rec go t =
          match t.Term.node with
          | Term.Param _ -> ()
          | Term.App (n, args) ->
            if Hashtbl.mem nodeset n then
              Hashtbl.replace counts n
                (1 + (try Hashtbl.find counts n with Not_found -> 0));
            Array.iter go args
        in
        go p.Grammar.rhs;
        Hashtbl.fold (fun q c acc -> (p.Grammar.name, q, c) :: acc) counts [])
      g
  in
  { nodes; edges }

(* in-degree of each node (= ref_G), as an association list *)
let in_degrees (net : t) : (string * int) list =
  let h = Hashtbl.create 256 in
  List.iter (fun n -> Hashtbl.replace h n 0) net.nodes;
  List.iter
    (fun (_, q, c) ->
      Hashtbl.replace h q (c + (try Hashtbl.find h q with Not_found -> 0)))
    net.edges;
  Hashtbl.fold (fun k v acc -> (k, v) :: acc) h []

(* Complementary cumulative distribution of in-degrees, for the log-log
   power-law plot (Fig. 1, O15): list of (k, P(X >= k)). *)
let ccdf (net : t) : (int * float) list =
  let degs = List.map snd (in_degrees net) in
  let n = List.length degs in
  if n = 0 then []
  else begin
    let maxd = List.fold_left max 0 degs in
    let counts = Array.make (maxd + 1) 0 in
    List.iter (fun d -> counts.(d) <- counts.(d) + 1) degs;
    let acc = ref 0 in
    let res = ref [] in
    for k = maxd downto 0 do
      acc := !acc + counts.(k);
      res := (k, float_of_int !acc /. float_of_int n) :: !res
    done;
    !res
  end

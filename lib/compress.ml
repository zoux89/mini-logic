(* Grammar-based proof-term compression (Sect. 5, 6).

   Two algorithms:

   - [dag_compress]: minimal DAG compression (arity-0 grammar). Every distinct
     subterm referenced more than once becomes its own (parameterless)
     production. This is the weakest compression; it already brings the
     gigantic tree sizes down (O11).

   - [treerepair]: TreeRePair, in the Sect. 6 variant that compresses the
     forest of a grammar's RHSs without ever expanding to ground trees. It
     repeatedly folds the most frequent digram

         f(V_1,..,V_{i-1}, g(V_i,..,V_{i+m-1}), V_{i+m},..,V_{n-1+m})

     into a fresh parametrised production, then prunes productions whose
     save-value is <= 0 (the pruning phase). Compressing the human grammar this
     way is how the paper discovers new shared lemmas (Sect. 6, App. B). *)

(* ----------------------------------------------------------------- *)
(* minimal DAG compression                                            *)
(* ----------------------------------------------------------------- *)

let dag_compress ?(start = "Start") (roots : Term.t list) : Grammar.t =
  (* Count references (parent edges, with multiplicity) to each distinct
     hash-consed subterm reachable from the roots. *)
  let refs : (int, int) Hashtbl.t = Hashtbl.create 4096 in
  let node : (int, Term.t) Hashtbl.t = Hashtbl.create 4096 in
  let bump t =
    Hashtbl.replace node t.Term.tag t;
    Hashtbl.replace refs t.Term.tag
      (1 + (try Hashtbl.find refs t.Term.tag with Not_found -> 0))
  in
  let seen : (int, unit) Hashtbl.t = Hashtbl.create 4096 in
  let rec walk t =
    (match t.Term.node with
     | Term.Param _ -> ()
     | Term.App (_, args) -> Array.iter bump args);
    if not (Hashtbl.mem seen t.Term.tag) then begin
      Hashtbl.replace seen t.Term.tag ();
      match t.Term.node with
      | Term.Param _ -> ()
      | Term.App (_, args) -> Array.iter walk args
    end
  in
  List.iter (fun r -> bump r; walk r) roots;
  (* A node is shared if it is an application of size >= 1 referenced >= 2x. *)
  let names : (int, string) Hashtbl.t = Hashtbl.create 256 in
  let ctr = ref 0 in
  let shared t =
    match t.Term.node with
    | Term.App (_, _) when Term.size t >= 1 ->
      (try Hashtbl.find refs t.Term.tag with Not_found -> 0) >= 2
    | _ -> false
  in
  let name_of t =
    match Hashtbl.find_opt names t.Term.tag with
    | Some n -> n
    | None ->
      incr ctr;
      let n = Printf.sprintf "d%d" !ctr in
      Hashtbl.replace names t.Term.tag n;
      n
  in
  (* Build the RHS of a shared node (or root): one level deep, replacing any
     shared child by a reference to its nonterminal. *)
  let rec build t =
    match t.Term.node with
    | Term.Param _ -> t
    | Term.App (n, args) ->
      Term.app n
        (Array.map (fun c -> if shared c then Term.leaf (name_of c) else build c) args)
  in
  (* Productions for every shared node, ordered so that referenced nonterminals
     come first (children before parents): emit in increasing size. *)
  let shared_nodes =
    Hashtbl.fold (fun tag t acc -> if shared t then (tag, t) :: acc else acc) node []
  in
  let shared_nodes =
    List.sort (fun (_, a) (_, b) -> compare (Term.size a) (Term.size b)) shared_nodes
  in
  let prods =
    List.map
      (fun (_, t) -> { Grammar.name = name_of t; arity = 0; rhs = build t })
      shared_nodes
  in
  let start_prods =
    List.map (fun r -> { Grammar.name = start; arity = 0; rhs = build r }) roots
  in
  prods @ start_prods

(* ----------------------------------------------------------------- *)
(* TreeRePair (replacement + pruning) over a forest of RHSs           *)
(* ----------------------------------------------------------------- *)

type msym = MApp of string | MParam of int
type mnode = { mutable sym : msym; mutable ch : mnode array }

let rec of_term (t : Term.t) : mnode =
  match t.Term.node with
  | Term.Param i -> { sym = MParam i; ch = [||] }
  | Term.App (n, args) -> { sym = MApp n; ch = Array.map of_term args }

let rec to_term (m : mnode) : Term.t =
  match m.sym with
  | MParam i -> Term.param i
  | MApp n -> Term.app n (Array.map to_term m.ch)

type slot = { sname : string; mutable sarity : int; mutable root : mnode }

(* digram key: parent name, parent arity, child index, child name, child arity *)
type digram = string * int * int * string * int

let treerepair ?(protect = fun _ -> false) (g : Grammar.t) : Grammar.t =
  let slots =
    List.map
      (fun p -> { sname = p.Grammar.name; sarity = p.Grammar.arity; root = of_term p.Grammar.rhs })
      g
  in
  let lemma_ctr = ref 0 in
  (* count digrams over the whole forest *)
  let count () : (digram, int) Hashtbl.t =
    let h = Hashtbl.create 1024 in
    let rec go n =
      (match n.sym with
       | MApp pf ->
         let pn = Array.length n.ch in
         Array.iteri
           (fun i c ->
             match c.sym with
             | MApp g ->
               let key = (pf, pn, i, g, Array.length c.ch) in
               Hashtbl.replace h key (1 + (try Hashtbl.find h key with Not_found -> 0))
             | MParam _ -> ())
           n.ch
       | MParam _ -> ());
      Array.iter go n.ch
    in
    List.iter (fun s -> go s.root) slots;
    h
  in
  let best (h : (digram, int) Hashtbl.t) : (digram * int) option =
    Hashtbl.fold
      (fun k v acc ->
        match acc with
        | Some (_, bv) when bv > v -> acc
        | Some (bk, bv) when bv = v && compare bk k <= 0 -> acc
        | _ -> Some (k, v))
      h None
  in
  (* fold every (non-overlapping, bottom-up) occurrence of [dg] into [h] *)
  let fold (((pf, pn, i, gname, gm) : digram)) (hname : string) : unit =
    let rec rw n =
      let ch = Array.map rw n.ch in
      let n = { sym = n.sym; ch } in
      match n.sym with
      | MApp f when String.equal f pf && Array.length ch = pn -> (
        match ch.(i).sym with
        | MApp g when String.equal g gname && Array.length ch.(i).ch = gm ->
          (* new children: f's children before i, g's children, f's after i *)
          let gch = ch.(i).ch in
          let before = Array.sub ch 0 i in
          let after = Array.sub ch (i + 1) (pn - i - 1) in
          { sym = MApp hname; ch = Array.concat [ before; gch; after ] }
        | _ -> n)
      | _ -> n
    in
    List.iter (fun s -> s.root <- rw s.root) slots
  in
  let new_slots = ref [] in
  let rec loop () =
    match best (count ()) with
    | Some (((pf, pn, i, gname, gm) as dg), v) when v >= 2 ->
      incr lemma_ctr;
      let hname = Printf.sprintf "lemma%d" !lemma_ctr in
      let harity = pn - 1 + gm in
      (* RHS pattern f(V_1,..,V_{i-1}, g(V_i,..), V_{i+m},..) with fresh params *)
      let pidx = ref 0 in
      let mkparam () = incr pidx; { sym = MParam !pidx; ch = [||] } in
      let before = Array.init i (fun _ -> mkparam ()) in
      let gch = Array.init gm (fun _ -> mkparam ()) in
      let after = Array.init (pn - i - 1) (fun _ -> mkparam ()) in
      let rhs =
        { sym = MApp pf;
          ch = Array.concat [ before; [| { sym = MApp gname; ch = gch } |]; after ] }
      in
      new_slots := { sname = hname; sarity = harity; root = rhs } :: !new_slots;
      fold dg hname;
      loop ()
    | _ -> ()
  in
  loop ();
  let all = slots @ List.rev !new_slots in
  let g0 : Grammar.t =
    List.map (fun s -> { Grammar.name = s.sname; arity = s.sarity; rhs = to_term s.root }) all
  in
  Order.prune ~protect (Order.topo g0)

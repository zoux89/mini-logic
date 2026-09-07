(* Proof terms (Sect. 2, Def. 1 of the paper).

   A proof term is built from
     - presupposition / nonterminal names [App (name, args)] with arity >= 0
       (a leaf axiom is just [App (name, [||])]), and
     - parameters [Param i] standing for the paper's V_i.

   Terms are hash-consed: structurally identical subterms share a single
   physical node, so identical subtrees collapse automatically. This gives us
   DAG sharing for free and makes [==]/[tag] equality the fast path used by the
   compression algorithms (digram detection, same-value reduction). *)

type node =
  | Param of int                  (* V_i, i >= 1 *)
  | App of string * t array
and t = { node : node; tag : int }

module Node = struct
  type t' = node
  type t = t'

  let equal a b =
    match a, b with
    | Param i, Param j -> i = j
    | App (f, fa), App (g, ga) ->
      String.equal f g
      && Array.length fa = Array.length ga
      &&
      let n = Array.length fa in
      let rec loop i = i >= n || (fa.(i) == ga.(i) && loop (i + 1)) in
      loop 0
    | _ -> false

  let hash = function
    | Param i -> Hashtbl.hash ("P", i)
    | App (f, args) ->
      let h = ref (Hashtbl.hash ("A", f, Array.length args)) in
      Array.iter (fun c -> h := (!h * 31) + c.tag) args;
      !h
end

module HC = Hashtbl.Make (Node)

let tbl : t HC.t = HC.create 4096
let counter = ref 0

let hashcons (node : node) : t =
  match HC.find_opt tbl node with
  | Some t -> t
  | None ->
    incr counter;
    let t = { node; tag = !counter } in
    HC.add tbl node t;
    t

let param i = hashcons (Param i)
let app name args = hashcons (App (name, args))
let leaf name = app name [||]

(* Physical (hash-consed) equality. *)
let equal (a : t) (b : t) = a == b

(* [size t] = number of edges of [t] viewed as a tree (Sect. 3):
   |V_i| = |leaf| = 0, |G(ax-1)| = 1, |D(G(ax-1),ax-2)| = 3. *)
let rec size (t : t) : int =
  match t.node with
  | Param _ -> 0
  | App (_, args) ->
    Array.fold_left (fun acc c -> acc + 1 + size c) 0 args

(* Largest parameter index occurring in [t] (0 if ground). *)
let rec max_param (t : t) : int =
  match t.node with
  | Param i -> i
  | App (_, args) -> Array.fold_left (fun acc c -> max acc (max_param c)) 0 args

let name_of (t : t) : string option =
  match t.node with App (n, _) -> Some n | Param _ -> None

let args_of (t : t) : t array =
  match t.node with App (_, a) -> a | Param _ -> [||]

(* Pretty-print a proof term, e.g. "D(ax-1, V1)". *)
let rec to_string (t : t) : string =
  match t.node with
  | Param i -> "V" ^ string_of_int i
  | App (name, [||]) -> name
  | App (name, args) ->
    name ^ "("
    ^ String.concat ", " (Array.to_list (Array.map to_string args))
    ^ ")"

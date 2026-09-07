(* Formula terms and definite clauses (Sect. 2).

   In CDDC every atom uses the same unary predicate "provable", so we represent
   an atom simply by its argument term [fterm]. Object-level connectives are
   ordinary function symbols, e.g. App ("->", [a; b]) for implication a => b,
   App ("A.", [x; p]) for universal quantification.

   A definite clause is [A <- B_1 /\ ... /\ B_n]. *)

type fterm =
  | Var of int
  | App of string * fterm list

type clause = { head : fterm; body : fterm list }

let counter = ref 0

let fresh () : fterm =
  incr counter;
  Var !counter

(* ----- substitutions (triangular, mutable store) ----- *)

type subst = (int, fterm) Hashtbl.t

let create_subst () : subst = Hashtbl.create 64

let rec deref (s : subst) (t : fterm) : fterm =
  match t with
  | Var i -> (
    match Hashtbl.find_opt s i with Some t' -> deref s t' | None -> t)
  | _ -> t

let rec occurs (s : subst) (i : int) (t : fterm) : bool =
  match deref s t with
  | Var j -> i = j
  | App (_, args) -> List.exists (occurs s i) args

let rec unify (s : subst) (a : fterm) (b : fterm) : bool =
  let a = deref s a and b = deref s b in
  match a, b with
  | Var i, Var j when i = j -> true
  | Var i, _ -> if occurs s i b then false else (Hashtbl.replace s i b; true)
  | _, Var j -> if occurs s j a then false else (Hashtbl.replace s j a; true)
  | App (f, fa), App (g, ga) ->
    String.equal f g
    && List.length fa = List.length ga
    && List.for_all2 (unify s) fa ga

let rec apply (s : subst) (t : fterm) : fterm =
  match deref s t with
  | Var i -> Var i
  | App (f, args) -> App (f, List.map (apply s) args)

(* Rename all variables of [t] to fresh ones, consistently via [m]. *)
let rec rename_with (m : (int, fterm) Hashtbl.t) (t : fterm) : fterm =
  match t with
  | Var i -> (
    match Hashtbl.find_opt m i with
    | Some v -> v
    | None ->
      let v = fresh () in
      Hashtbl.replace m i v;
      v)
  | App (f, args) -> App (f, List.map (rename_with m) args)

let rename_clause (c : clause) : clause =
  let m = Hashtbl.create 16 in
  { head = rename_with m c.head; body = List.map (rename_with m) c.body }

(* ----- equality up to renaming of variables (alpha-equivalence) ----- *)

let alpha_eq_clause (c1 : clause) (c2 : clause) : bool =
  if List.length c1.body <> List.length c2.body then false
  else begin
    let m12 = Hashtbl.create 16 and m21 = Hashtbl.create 16 in
    let rec go a b =
      match a, b with
      | Var i, Var j -> (
        match Hashtbl.find_opt m12 i, Hashtbl.find_opt m21 j with
        | None, None ->
          Hashtbl.replace m12 i j;
          Hashtbl.replace m21 j i;
          true
        | Some j', Some i' -> j' = j && i' = i
        | _ -> false)
      | App (f, fa), App (g, ga) ->
        String.equal f g
        && List.length fa = List.length ga
        && List.for_all2 go fa ga
      | _ -> false
    in
    go c1.head c2.head && List.for_all2 go c1.body c2.body
  end

(* ----- convenience constructors / pretty printing ----- *)

let imp a b = App ("->", [ a; b ])
let v i = Var i

let rec term_to_string (t : fterm) : string =
  match t with
  | Var i -> "x" ^ string_of_int i
  | App ("->", [ a; b ]) ->
    "( " ^ term_to_string a ^ " -> " ^ term_to_string b ^ " )"
  | App (f, []) -> f
  | App (f, args) ->
    f ^ "(" ^ String.concat ", " (List.map term_to_string args) ^ ")"

let clause_to_string (c : clause) : string =
  match c.body with
  | [] -> term_to_string c.head
  | _ ->
    term_to_string c.head ^ " <- "
    ^ String.concat " /\\ " (List.map term_to_string c.body)

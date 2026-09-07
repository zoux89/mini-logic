(* Pluggable proof-source backend (Sect. 7).

   The engine (compression + analysis + visualization) only consumes a
   [loaded] value, so it is completely source-agnostic. Metamath provides the
   working backend; Lean/mathlib is a stub for a future translation. *)

type loaded = {
  grammar : Grammar.t;                 (* one production per theorem proof *)
  statement : string -> string option; (* stated formula for a name, verbatim *)
  essentials : string -> string list;  (* essential-hypothesis statements *)
  is_axiom : string -> bool;           (* true for terminals / presuppositions *)
  vartypes : (string * string) list;   (* variable token -> typecode, for rendering *)
}

type t = { name : string; load : limit:int -> path:string -> loaded }

(* ---- Metamath backend ---- *)

let metamath : t =
  {
    name = "metamath";
    load =
      (fun ~limit ~path ->
        let ic = open_in_bin path in
        let n = in_channel_length ic in
        let text = really_input_string ic n in
        close_in ic;
        let db = Metamath.parse ~max_theorems:limit text in
        let grammar = Metamath.grammar_of_db db in
        let info name = Hashtbl.find_opt db.Metamath.table name in
        {
          grammar;
          statement = (fun n -> match info n with Some t -> Some t.Metamath.statement | None -> None);
          essentials = (fun n -> match info n with Some t -> t.Metamath.ess | None -> []);
          is_axiom = (fun n -> match info n with Some t -> t.Metamath.is_axiom | None -> false);
          vartypes = Hashtbl.fold (fun v tc acc -> (v, tc) :: acc) db.Metamath.vartypes [];
        });
  }

(* ---- Lean / mathlib backend (stub) ----

   Lean's calculus is dependent type theory, not condensed detachment, so its
   proofs do not map directly onto D/G proof terms; a dedicated translation
   (paper Sect. 7) would be required before this backend can yield proof
   grammars for the same compression engine. *)

let lean : t =
  {
    name = "lean";
    load =
      (fun ~limit:_ ~path:_ ->
        failwith
          "Lean/mathlib backend is not implemented yet (needs a dependent-type \
           to condensed-detachment translation; see Sect. 7).");
  }

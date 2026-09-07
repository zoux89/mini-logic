(* Metamath (set.mm) ingester (Sect. 7).

   We parse a Metamath database and turn each theorem's proof into a *proof
   term* (Sect. 2): the syntactic, wff-building steps are dropped (line 251) and
   every logical (|- ) step becomes a function symbol applied to the proof terms
   of its essential hypotheses. Axioms ($a with |- ) become terminals
   (presupposition names); theorems ($p) become productions of the proof
   grammar, with arity = number of essential mandatory hypotheses.

   This is the source-agnostic [Backend] for the engine; the compression and
   visualization never look at Metamath again. *)

(* ---------- streaming tokenizer (comments / includes stripped) ---------- *)

type cursor = { s : string; len : int; mutable pos : int }

let is_ws c = c = ' ' || c = '\t' || c = '\n' || c = '\r'

let raw_token (c : cursor) : string option =
  while c.pos < c.len && is_ws c.s.[c.pos] do c.pos <- c.pos + 1 done;
  if c.pos >= c.len then None
  else begin
    let start = c.pos in
    while c.pos < c.len && not (is_ws c.s.[c.pos]) do c.pos <- c.pos + 1 done;
    Some (String.sub c.s start (c.pos - start))
  end

(* token stream skipping $( ... $) comments and $[ ... $] includes *)
let rec next (c : cursor) : string option =
  match raw_token c with
  | None -> None
  | Some "$(" ->
    let rec skip () =
      match raw_token c with Some "$)" -> next c | None -> None | Some _ -> skip ()
    in
    skip ()
  | Some "$[" ->
    let rec skip () =
      match raw_token c with Some "$]" -> next c | None -> None | Some _ -> skip ()
    in
    skip ()
  | tok -> tok

let read_until (c : cursor) (terms : string list) : string list * string =
  let rec go acc =
    match next c with
    | None -> (List.rev acc, "")
    | Some t when List.mem t terms -> (List.rev acc, t)
    | Some t -> go (t :: acc)
  in
  go []

(* ---------- database model ---------- *)

type hkind = HF | HE

type hyp = { hl : string; hk : hkind; hvar : string option; hsyms : string list }

type asrt = {
  tc : string;
  mand : (string * bool) list; (* (label, is_essential) in mandatory order *)
  stmt : string;               (* conclusion symbols, space-joined *)
  ess : string list;           (* essential-hypothesis statements, in order *)
  isp : bool;                  (* true if $p, false if $a *)
}

type entry = Hyp of hyp | Asrt of asrt

type theorem = {
  label : string;
  is_axiom : bool;  (* $a with |- typecode -> terminal/presupposition *)
  arity : int;
  proof : Term.t option;
  statement : string;
  ess : string list;
  typecode : string;
}

type db = {
  order : string list;
  table : (string, theorem) Hashtbl.t;
  vartypes : (string, string) Hashtbl.t; (* variable token -> typecode (wff/setvar/class) *)
}

(* ---------- compressed / normal proof decoding ---------- *)

type action = ARef of int | ASave

let decode_compressed (labels : string array) (m : int) (enc : string) :
    action list =
  (* labels: combined [mandatory hyps (m) ; parenthesised labels]. *)
  ignore labels;
  let acts = ref [] in
  let n = ref 0 in
  String.iter
    (fun ch ->
      if ch >= 'A' && ch <= 'T' then begin
        let num = (!n * 20) + (Char.code ch - Char.code 'A') + 1 in
        n := 0;
        acts := ARef num :: !acts
      end
      else if ch >= 'U' && ch <= 'Y' then
        n := (!n * 5) + (Char.code ch - Char.code 'U') + 1
      else if ch = 'Z' then acts := ASave :: !acts
      else () (* '?' or stray: leave; caller may fail to build *))
    enc;
  ignore m;
  List.rev !acts

(* ---------- extraction ---------- *)

type pentry = Wff | Pf of Term.t

exception Extract_fail

let take n l = (* first n elements *)
  let rec go i acc l =
    if i = 0 then List.rev acc
    else match l with x :: r -> go (i - 1) (x :: acc) r | [] -> List.rev acc
  in
  go n [] l

let parse ?(max_theorems = max_int) (text : string) : db =
  let c = { s = text; len = String.length text; pos = 0 } in
  let consts : (string, unit) Hashtbl.t = Hashtbl.create 1024 in
  let vars : (string, unit) Hashtbl.t = Hashtbl.create 1024 in
  let reg : (string, entry) Hashtbl.t = Hashtbl.create 4096 in
  let active : hyp list ref = ref [] in
  let marks : int list ref = ref [] in
  let order = ref [] in
  let table : (string, theorem) Hashtbl.t = Hashtbl.create 4096 in
  let vartypes : (string, string) Hashtbl.t = Hashtbl.create 256 in
  let nthm = ref 0 in

  let is_var t = Hashtbl.mem vars t in

  (* mandatory hyps of an assertion whose conclusion + essential hyps use the
     given symbol lists *)
  let mandatory (concl : string list) : (string * bool) list * hyp list =
    let needed = Hashtbl.create 32 in
    let mark_vars syms = List.iter (fun t -> if is_var t then Hashtbl.replace needed t ()) syms in
    mark_vars concl;
    List.iter (fun h -> if h.hk = HE then mark_vars h.hsyms) !active;
    let keep h =
      match h.hk with
      | HE -> true
      | HF -> (match h.hvar with Some v -> Hashtbl.mem needed v | None -> false)
    in
    let hyps = List.filter keep !active in
    (List.map (fun h -> (h.hl, h.hk = HE)) hyps, hyps)
  in

  let extract_proof (mand : (string * bool) list) (paren : string list)
      (enc_or_labels : [ `Comp of string | `Normal of string list ]) :
      Term.t option =
    (* essential hyp param indices for this theorem *)
    let ess_idx : (string, int) Hashtbl.t = Hashtbl.create 16 in
    let i = ref 0 in
    List.iter (fun (l, e) -> if e then (incr i; Hashtbl.replace ess_idx l !i)) mand;
    let mand_labels = Array.of_list (List.map fst mand) in
    let m = Array.length mand_labels in
    let paren_arr = Array.of_list paren in
    let k = Array.length paren_arr in
    let combined = Array.append mand_labels paren_arr in
    let saved : pentry list ref = ref [] in
    let stack : pentry list ref = ref [] in
    let push e = stack := e :: !stack in
    let process_label (l : string) : unit =
      match Hashtbl.find_opt reg l with
      | None -> raise Extract_fail
      | Some (Hyp h) -> (
        match h.hk with
        | HF -> push Wff
        | HE -> (
          match Hashtbl.find_opt ess_idx l with
          | Some idx -> push (Pf (Term.param idx))
          | None -> raise Extract_fail))
      | Some (Asrt a) ->
        let len = List.length a.mand in
        if List.length !stack < len then raise Extract_fail;
        let popped = Array.make len Wff in
        for j = len - 1 downto 0 do
          (match !stack with e :: r -> popped.(j) <- e; stack := r | [] -> raise Extract_fail)
        done;
        if String.equal a.tc "|-" then begin
          let children = ref [] in
          List.iteri
            (fun j (_, is_ess) ->
              if is_ess then
                match popped.(j) with
                | Pf t -> children := t :: !children
                | Wff -> raise Extract_fail)
            a.mand;
          push (Pf (Term.app l (Array.of_list (List.rev !children))))
        end
        else push Wff
    in
    let do_ref num =
      if num >= 1 && num <= m + k then process_label combined.(num - 1)
      else begin
        let s = num - m - k in (* 1-based into saved *)
        match List.nth_opt !saved (s - 1) with
        | Some e -> push e
        | None -> raise Extract_fail
      end
    in
    try
      (match enc_or_labels with
       | `Comp enc ->
         List.iter
           (function
             | ARef num -> do_ref num
             | ASave -> ( match !stack with e :: _ -> saved := !saved @ [ e ] | [] -> raise Extract_fail))
           (decode_compressed combined m enc)
       | `Normal labels -> List.iter process_label labels);
      match !stack with [ Pf t ] -> Some t | _ -> None
    with Extract_fail -> None
  in

  let rec loop () =
    if !nthm >= max_theorems then ()
    else
      match next c with
      | None -> ()
      | Some "${" -> marks := List.length !active :: !marks; loop ()
      | Some "$}" ->
        (match !marks with
         | n :: r -> active := take n !active; marks := r
         | [] -> ());
        loop ()
      | Some "$c" -> let toks, _ = read_until c [ "$." ] in List.iter (fun t -> Hashtbl.replace consts t ()) toks; loop ()
      | Some "$v" -> let toks, _ = read_until c [ "$." ] in List.iter (fun t -> Hashtbl.replace vars t ()) toks; loop ()
      | Some "$d" -> let _ = read_until c [ "$." ] in loop ()
      | Some "$(" -> loop () (* shouldn't happen, next strips comments *)
      | Some lbl ->
        (* a labelled statement: next token is the keyword *)
        (match next c with
         | Some "$f" ->
           let toks, _ = read_until c [ "$." ] in
           (match toks with
            | tc :: var :: _ ->
              Hashtbl.replace vartypes var tc;
              let h = { hl = lbl; hk = HF; hvar = Some var; hsyms = [ var ] } in
              Hashtbl.replace reg lbl (Hyp h);
              active := !active @ [ h ]
            | _ -> ());
           loop ()
         | Some "$e" ->
           let toks, _ = read_until c [ "$." ] in
           (match toks with
            | tc :: syms ->
              ignore tc;
              let h = { hl = lbl; hk = HE; hvar = None; hsyms = syms } in
              Hashtbl.replace reg lbl (Hyp h);
              active := !active @ [ h ]
            | _ -> ());
           loop ()
         | Some "$a" ->
           let toks, _ = read_until c [ "$." ] in
           (match toks with
            | tc :: syms ->
              let mand, hyps = mandatory syms in
              let ess = List.filter_map (fun h -> if h.hk = HE then Some (String.concat " " h.hsyms) else None) hyps in
              let stmt = String.concat " " syms in
              Hashtbl.replace reg lbl (Asrt { tc; mand; stmt; ess; isp = false });
              if String.equal tc "|-" then begin
                order := lbl :: !order;
                Hashtbl.replace table lbl
                  { label = lbl; is_axiom = true;
                    arity = List.length (List.filter snd mand);
                    proof = None; statement = stmt; ess; typecode = tc }
              end
            | _ -> ());
           loop ()
         | Some "$p" ->
           let syms, _ = read_until c [ "$=" ] in
           let proof_toks, _ = read_until c [ "$." ] in
           (match syms with
            | tc :: concl ->
              let mand, hyps = mandatory concl in
              let ess = List.filter_map (fun h -> if h.hk = HE then Some (String.concat " " h.hsyms) else None) hyps in
              let stmt = String.concat " " concl in
              (* decode proof: compressed "( labels ) ENC" or normal labels *)
              let proof =
                match proof_toks with
                | "(" :: rest ->
                  (* split rest at ")" *)
                  let rec split acc = function
                    | ")" :: enc -> (List.rev acc, String.concat "" enc)
                    | x :: r -> split (x :: acc) r
                    | [] -> (List.rev acc, "")
                  in
                  let paren, enc = split [] rest in
                  extract_proof mand paren (`Comp enc)
                | labels -> extract_proof mand [] (`Normal labels)
              in
              (* register as assertion so later proofs can reference it *)
              Hashtbl.replace reg lbl (Asrt { tc; mand; stmt; ess; isp = true });
              if String.equal tc "|-" then begin
                order := lbl :: !order;
                Hashtbl.replace table lbl
                  { label = lbl; is_axiom = false;
                    arity = List.length (List.filter snd mand);
                    proof; statement = stmt; ess; typecode = tc };
                incr nthm
              end
            | _ -> ());
           loop ()
         | Some other ->
           (* unknown keyword after label; skip to $. *)
           if other = "$." then () else (let _ = read_until c [ "$." ] in ());
           loop ()
         | None -> ())
  in
  loop ();
  { order = List.rev !order; table; vartypes }

(* Build the proof grammar: one production per $p theorem with a successfully
   extracted proof. Axioms ($a |- ) are terminals and do not get productions. *)
let grammar_of_db (d : db) : Grammar.t =
  List.filter_map
    (fun lbl ->
      match Hashtbl.find_opt d.table lbl with
      | Some th -> (
        match th.proof with
        | Some p when not th.is_axiom ->
          Some { Grammar.name = lbl; arity = th.arity; rhs = p }
        | _ -> None)
      | None -> None)
    d.order

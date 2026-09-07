open Mini_math

(* set.mm pinned to the paper's commit (Sect. 1, line 23). raw.githubusercontent
   serves a full file by commit SHA; override with: main fetch <url> <path>. *)
let setmm_commit = "8cf01a7"
let setmm_url =
  Printf.sprintf "https://raw.githubusercontent.com/metamath/set.mm/%s/set.mm"
    setmm_commit
let default_path = "data/set.mm"

let sh cmd = ignore (Sys.command cmd)

let fetch url path =
  sh "mkdir -p data";
  Printf.printf "Downloading set.mm (commit %s) -> %s\n%!" setmm_commit path;
  let code = Sys.command (Printf.sprintf "curl -fL -o %s %s" (Filename.quote path) (Filename.quote url)) in
  if code <> 0 then (Printf.eprintf "curl failed (exit %d). Provide a URL/path manually.\n" code; exit 1)

(* ---------- JSON encoding of a grammar + analysis ---------- *)

let rec term_json (t : Term.t) : Json.t =
  match t.Term.node with
  | Term.Param i -> Json.Obj [ ("v", Json.Int i) ]
  | Term.App (n, args) ->
    Json.Obj
      [ ("s", Json.Str n);
        ("c", Json.List (Array.to_list (Array.map term_json args))) ]

let names_of (g : Grammar.t) : (string, unit) Hashtbl.t =
  let h = Hashtbl.create 512 in
  List.iter
    (fun p ->
      Hashtbl.replace h p.Grammar.name ();
      let rec go t =
        match t.Term.node with
        | Term.Param _ -> ()
        | Term.App (n, args) -> Hashtbl.replace h n (); Array.iter go args
      in
      go p.Grammar.rhs)
    g;
  h

let kind_of (bk : Backend.loaded) (name : string) : string =
  if bk.Backend.is_axiom name then "axiom"
  else match bk.Backend.statement name with Some _ -> "thm" | None -> "lemma"

let statement_of (bk : Backend.loaded) (g : Grammar.t) (name : string) : string =
  match bk.Backend.statement name with
  | Some s -> s
  | None -> (
    match Grammar.find g name with
    | Some p -> "= " ^ Term.to_string p.Grammar.rhs
    | None -> "")

let grammar_json (bk : Backend.loaded) (g : Grammar.t) : Json.t =
  let names = names_of g in
  let productions =
    List.map
      (fun p ->
        ( p.Grammar.name,
          Json.Obj [ ("arity", Json.Int p.Grammar.arity); ("rhs", term_json p.Grammar.rhs) ] ))
      g
  in
  let info =
    Hashtbl.fold
      (fun name () acc ->
        let sav = match Grammar.find g name with Some p -> Grammar.save_value g p | None -> 0 in
        ( name,
          Json.Obj
            [ ("statement", Json.Str (statement_of bk g name));
              ("ess", Json.List (List.map (fun s -> Json.Str s) (bk.Backend.essentials name)));
              ("kind", Json.Str (kind_of bk name));
              ("ref", Json.Int (Grammar.ref_count g name));
              ("sav", Json.Int sav) ] )
        :: acc)
      names []
  in
  let roots =
    List.filter_map
      (fun p -> if Grammar.ref_count g p.Grammar.name = 0 then Some (Json.Str p.Grammar.name) else None)
      g
  in
  let net = Pdnet.of_grammar g in
  let pdnet =
    Json.Obj
      [ ("nodes", Json.List (List.map (fun n -> Json.Str n) net.Pdnet.nodes));
        ( "edges",
          Json.List
            (List.map (fun (p, q, c) -> Json.List [ Json.Str p; Json.Str q; Json.Int c ]) net.Pdnet.edges) ) ]
  in
  let ccdf =
    Json.List (List.map (fun (k, pr) -> Json.List [ Json.Int k; Json.Float pr ]) (Pdnet.ccdf net))
  in
  Json.Obj
    [ ("size", Json.Int (Grammar.size g));
      ("num", Json.Int (Grammar.num_productions g));
      ("productions", Json.Obj productions);
      ("info", Json.Obj info);
      ("roots", Json.List roots);
      ("pdnet", pdnet);
      ("ccdf", ccdf) ]

let load ~limit ~path : Backend.loaded =
  if not (Sys.file_exists path) then (
    Printf.eprintf "set.mm not found at %s. Run: main fetch\n" path; exit 1);
  Backend.metamath.Backend.load ~limit ~path

let run_export ~limit ~path =
  Printf.printf "Loading %s (first %d theorems)...\n%!" path limit;
  let bk = load ~limit ~path in
  let human = bk.Backend.grammar in
  Printf.printf "Human grammar:  |G| = %d, productions = %d\n%!"
    (Grammar.size human) (Grammar.num_productions human);
  let orig = Hashtbl.create 1024 in
  List.iter (fun p -> Hashtbl.replace orig p.Grammar.name ()) human;
  let protect n = Hashtbl.mem orig n in
  Printf.printf "Compressing (TreeRePair, Sect. 6)...\n%!";
  let machine = Compress.treerepair ~protect human in
  let new_lemmas =
    List.length (List.filter (fun p -> not (Hashtbl.mem orig p.Grammar.name)) machine)
  in
  let reduction =
    if Grammar.size human = 0 then 0.0
    else
      100.0 *. float_of_int (Grammar.size human - Grammar.size machine)
      /. float_of_int (Grammar.size human)
  in
  Printf.printf "Machine grammar: |G| = %d, productions = %d  (reduction %.1f%%, %d new lemmas)\n%!"
    (Grammar.size machine) (Grammar.num_productions machine) reduction new_lemmas;
  let data =
    Json.Obj
      [ ("commit", Json.Str setmm_commit);
        ("limit", Json.Int limit);
        ("vartypes", Json.Obj (List.map (fun (v, tc) -> (v, Json.Str tc)) bk.Backend.vartypes));
        ("human", grammar_json bk human);
        ("machine", grammar_json bk machine) ]
  in
  sh "mkdir -p visualization/data";
  let oc = open_out "visualization/data/data.json" in
  output_string oc (Json.to_string data);
  close_out oc;
  Printf.printf "Wrote visualization/data/data.json\n%!"

(* Correctness check: unfolding every inserted lemma in the machine grammar
   must reproduce each original human proof term exactly (lossless). *)
let run_verify ~limit ~path =
  let bk = load ~limit ~path in
  let human = bk.Backend.grammar in
  let orig = Hashtbl.create 1024 in
  List.iter (fun p -> Hashtbl.replace orig p.Grammar.name ()) human;
  let protect n = Hashtbl.mem orig n in
  let machine = Compress.treerepair ~protect human in
  (* lemma definitions = machine productions whose name is not original *)
  let lemmas = Hashtbl.create 1024 in
  List.iter
    (fun p -> if not (Hashtbl.mem orig p.Grammar.name) then Hashtbl.replace lemmas p.Grammar.name p)
    machine;
  let rec unfold t =
    match t.Term.node with
    | Term.Param _ -> t
    | Term.App (n, args) ->
      let args = Array.map unfold args in
      (match Hashtbl.find_opt lemmas n with
       | Some p -> unfold (Grammar.subst_params p.Grammar.rhs args)
       | None -> Term.app n args)
  in
  let mtbl = Hashtbl.create 4096 in
  List.iter (fun p -> Hashtbl.replace mtbl p.Grammar.name p) machine;
  let ok = ref 0 and bad = ref 0 in
  List.iter
    (fun hp ->
      match Hashtbl.find_opt mtbl hp.Grammar.name with
      | Some mp -> if Term.equal (unfold mp.Grammar.rhs) hp.Grammar.rhs then incr ok else incr bad
      | None -> incr bad)
    human;
  Printf.printf
    "verify: %d/%d original proofs reproduced exactly after unfolding %d lemmas (|G| %d -> %d)\n"
    !ok (!ok + !bad) (Hashtbl.length lemmas) (Grammar.size human) (Grammar.size machine);
  if !bad > 0 then exit 1

let () =
  match Array.to_list Sys.argv with
  | _ :: "verify" :: rest ->
    let limit = match rest with l :: _ -> int_of_string l | [] -> 1000 in
    let path = match rest with _ :: p :: _ -> p | _ -> default_path in
    run_verify ~limit ~path
  | _ :: "fetch" :: rest ->
    let url = match rest with u :: _ -> u | [] -> setmm_url in
    let path = match rest with _ :: p :: _ -> p | _ -> default_path in
    fetch url path
  | _ :: "export" :: rest ->
    let limit = match rest with l :: _ -> int_of_string l | [] -> 200 in
    let path = match rest with _ :: p :: _ -> p | _ -> default_path in
    run_export ~limit ~path
  | _ ->
    print_string
      "mini-math: grammar-compressed Metamath proof structures\n\n\
       Usage:\n\
      \  main fetch [url] [path]       download set.mm (default commit pinned)\n\
      \  main export [limit] [path]    parse a fragment, compress, write \
       visualization/data/data.json\n\
      \  main verify [limit] [path]    prove the compression is lossless \
       (unfold lemmas == original proofs)\n"

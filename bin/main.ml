open Mini_math

(* set.mm pinned to the paper's commit (Sect. 1). Override with:
   main fetch <url> <path>. *)
let setmm_commit = "8cf01a7"
let setmm_url =
  Printf.sprintf "https://raw.githubusercontent.com/metamath/set.mm/%s/set.mm"
    setmm_commit
let default_path = "data/set.mm"

let fetch url path =
  let dir = Filename.dirname path in
  if not (Sys.file_exists dir) then Sys.mkdir dir 0o755;
  Printf.printf "Downloading set.mm (commit %s) -> %s\n%!" setmm_commit path;
  let code =
    Sys.command
      (Printf.sprintf "curl -fL -o %s %s" (Filename.quote path) (Filename.quote url))
  in
  if code <> 0 then begin
    Printf.eprintf "curl failed (exit %d). Provide a URL/path manually.\n" code;
    exit 1
  end

let load ~limit ~path : Grammar.t =
  if not (Sys.file_exists path) then begin
    Printf.eprintf "set.mm not found at %s. Run: main fetch\n" path;
    exit 1
  end;
  Metamath.grammar_of_db (Metamath.load ~max_theorems:limit path)

(* Human grammar -> machine grammar: TreeRePair over the RHS forest with the
   original theorems protected from pruning (Sect. 6). Returns the machine
   grammar and the sub-grammar of newly introduced lemmas. *)
let compress (human : Grammar.t) : Grammar.t * Grammar.t =
  let orig = Grammar.table human in
  let protect n = Hashtbl.mem orig n in
  let machine = Compress.treerepair ~protect human in
  let lemmas = List.filter (fun p -> not (Hashtbl.mem orig p.Grammar.name)) machine in
  (machine, lemmas)

(* ---------- stats (a text rendering of the paper's Table 2 block) ---------- *)

let pct part total =
  if total = 0 then 0.0 else 100.0 *. float_of_int part /. float_of_int total

let print_dist label (xs : int list) =
  match xs with
  | [] -> Printf.printf "  %-10s (none)\n" label
  | _ ->
    let a = Array.of_list xs in
    Array.sort compare a;
    let n = Array.length a in
    let sum = Array.fold_left ( + ) 0 a in
    let median =
      if n mod 2 = 1 then float_of_int a.(n / 2)
      else float_of_int (a.((n / 2) - 1) + a.(n / 2)) /. 2.0
    in
    Printf.printf "  %-10s min %d   median %.0f   mean %.1f   max %d   sum %d\n"
      label a.(0) median (float_of_int sum /. float_of_int n) a.(n - 1) sum

let run_stats ~limit ~path =
  Printf.printf "Loading %s (first %d theorems)...\n%!" path limit;
  let human = load ~limit ~path in
  let n = Grammar.num_productions human in
  Printf.printf "\nHuman grammar (set.mm)\n";
  Printf.printf "  |G| = %d   N(G) = %d\n" (Grammar.size human) n;
  let refs = List.map (fun p -> Grammar.ref_count human p.Grammar.name) human in
  print_dist "ref_G(p)" refs;
  Printf.printf "  %-10s ref=0: %.1f%%   ref=1: %.1f%%\n" ""
    (pct (List.length (List.filter (( = ) 0) refs)) n)
    (pct (List.length (List.filter (( = ) 1) refs)) n);
  print_dist "|p|" (List.map Grammar.production_size human);
  let savs =
    List.filter_map
      (fun p ->
        if Grammar.ref_count human p.Grammar.name > 0 then
          Some (Grammar.save_value human p)
        else None)
      human
  in
  print_dist "sav_G(p)" savs;
  Printf.printf "  %-10s (over ref>0) sav<0: %.1f%%   sav=0: %.1f%%\n" ""
    (pct (List.length (List.filter (fun s -> s < 0) savs)) (List.length savs))
    (pct (List.length (List.filter (( = ) 0) savs)) (List.length savs));
  let arities = List.map (fun p -> p.Grammar.arity) human in
  print_dist "arity(p)" arities;
  Printf.printf "  %-10s arity=0: %.1f%%\n" ""
    (pct (List.length (List.filter (( = ) 0) arities)) n);
  Printf.printf "  %-10s %.1f%% of productions are nonlinear\n" "nl_G"
    (pct (List.length (List.filter (fun p -> not (Grammar.is_linear p)) human)) n);
  Printf.printf "\nCompressing (TreeRePair over RHS forest, originals protected)...\n%!";
  let machine, lemmas = compress human in
  Printf.printf "Machine grammar\n";
  Printf.printf "  |G| = %d   N(G) = %d   reduction %.1f%%   new lemmas %d\n"
    (Grammar.size machine) (Grammar.num_productions machine)
    (pct (Grammar.size human - Grammar.size machine) (Grammar.size human))
    (List.length lemmas);
  let ranked =
    List.map (fun p -> (Grammar.save_value machine p, p)) lemmas
    |> List.sort (fun (a, p) (b, q) ->
           match compare b a with 0 -> compare p.Grammar.name q.Grammar.name | c -> c)
  in
  Printf.printf "\nTop new lemmas by save-value (cf. App. B)\n";
  List.iteri
    (fun i (sav, p) ->
      if i < 10 then begin
        let params =
          if p.Grammar.arity = 0 then ""
          else
            "("
            ^ String.concat ", "
                (List.init p.Grammar.arity (fun j -> "V" ^ string_of_int (j + 1)))
            ^ ")"
        in
        Printf.printf "  %s%s -> %s\n      sav=%d  |p|=%d  ref=%d\n" p.Grammar.name params
          (Term.to_string p.Grammar.rhs) sav (Grammar.production_size p)
          (Grammar.ref_count machine p.Grammar.name)
      end)
    ranked

(* ---------- verify (lossless) ---------- *)

(* Unfolding every inserted lemma in the machine grammar must reproduce each
   original human proof term exactly: val_lemmas(rhs_machine(p)) = rhs_human(p). *)
let run_verify ~limit ~path =
  let human = load ~limit ~path in
  let machine, lemmas = compress human in
  let mtbl = Grammar.table machine in
  let ok = ref 0 and bad = ref 0 in
  List.iter
    (fun hp ->
      match Hashtbl.find_opt mtbl hp.Grammar.name with
      | Some mp when Term.equal (Grammar.value lemmas mp.Grammar.rhs) hp.Grammar.rhs ->
        incr ok
      | _ -> incr bad)
    human;
  Printf.printf
    "verify: %d/%d original proofs reproduced exactly after unfolding %d lemmas (|G| %d -> %d)\n"
    !ok (!ok + !bad) (List.length lemmas) (Grammar.size human) (Grammar.size machine);
  if !bad > 0 then exit 1

let usage =
  "mini-math: grammar-compressed Metamath proof structures\n\n\
   Usage:\n\
  \  main fetch [url] [path]     download set.mm (default: paper's pinned commit -> data/set.mm)\n\
  \  main stats [limit] [path]   grammar statistics (Table 2 style) and top new lemmas after TreeRePair\n\
  \  main verify [limit] [path]  check the compression is lossless (unfold lemmas == original proofs)\n"

let () =
  let limit_path rest default =
    let limit = match rest with l :: _ -> int_of_string l | [] -> default in
    let path = match rest with _ :: p :: _ -> p | _ -> default_path in
    (limit, path)
  in
  match Array.to_list Sys.argv with
  | _ :: "fetch" :: rest ->
    let url = match rest with u :: _ -> u | [] -> setmm_url in
    let path = match rest with _ :: p :: _ -> p | _ -> default_path in
    fetch url path
  | _ :: "stats" :: rest ->
    let limit, path = limit_path rest 1000 in
    run_stats ~limit ~path
  | _ :: "verify" :: rest ->
    let limit, path = limit_path rest 1000 in
    run_verify ~limit ~path
  | _ -> print_string usage

open Mini_math

let failures = ref 0
let total = ref 0

let check name cond =
  incr total;
  if cond then Printf.printf "  ok   %s\n" name
  else begin
    incr failures;
    Printf.printf "  FAIL %s\n" name
  end

(* ----- Example 3 base (Sect. 2) ----- *)
(* B = { D :: y <- (x=>y) /\ x,
         ax-1 :: x1 => (x2 => x1),
         ax-2 :: (x1=>(x2=>x3)) => ((x1=>x2)=>(x1=>x3)) } *)

let fv = Formula.v
let ( ==> ) = Formula.imp

let base =
  Cddc.base_of_list
    [
      ("D", { Formula.head = fv 2; body = [ (fv 1 ==> fv 2); fv 1 ] });
      ("ax-1", { Formula.head = fv 1 ==> (fv 2 ==> fv 1); body = [] });
      ( "ax-2",
        {
          Formula.head =
            (fv 1 ==> (fv 2 ==> fv 3))
            ==> ((fv 1 ==> fv 2) ==> (fv 1 ==> fv 3));
          body = [];
        } );
    ]

(* proof-term constructors *)
let d a b = Term.app "D" [| a; b |]
let ax1 = Term.leaf "ax-1"
let ax2 = Term.leaf "ax-2"
let pV1 = Term.param 1

let mgt_eq term expected =
  match Cddc.mgt base term with
  | None -> false
  | Some c -> Formula.alpha_eq_clause c expected

let mgt_undef term = Cddc.mgt base term = None

let () =
  print_endline "== Example 3 (mgt) ==";

  (* (i) mgt(ax-1) = x1 => (x2 => x1) *)
  check "3(i) ax-1"
    (mgt_eq ax1 { Formula.head = fv 1 ==> (fv 2 ==> fv 1); body = [] });

  (* (ii) mgt(D(ax-1,ax-1)) = x1 => (x2 => (x3 => x2)) *)
  check "3(ii) D(ax-1,ax-1)"
    (mgt_eq (d ax1 ax1)
       { Formula.head = fv 1 ==> (fv 2 ==> (fv 3 ==> fv 2)); body = [] });

  (* (iii) mgt(D(V1,ax-1)) = x1 <- ((x2 => (x3 => x2)) => x1) *)
  check "3(iii) D(V1,ax-1)"
    (mgt_eq (d pV1 ax1)
       { Formula.head = fv 1;
         body = [ (fv 2 ==> (fv 3 ==> fv 2)) ==> fv 1 ] });

  (* (v) mgt(D(D(ax-2,ax-2),ax-2)) is undefined *)
  check "3(v) D(D(ax-2,ax-2),ax-2) undefined" (mgt_undef (d (d ax2 ax2) ax2));

  (* (vii) mgt(D(D(ax-2,ax-1),ax-2)) =
           ((x1=>(x2=>x3)) => (x1=>(x2=>x3))) *)
  check "3(vii) D(D(ax-2,ax-1),ax-2)"
    (mgt_eq (d (d ax2 ax1) ax2)
       {
         Formula.head =
           (fv 1 ==> (fv 2 ==> fv 3)) ==> (fv 1 ==> (fv 2 ==> fv 3));
         body = [];
       });

  print_endline "== Example 6 (grammar sizes / val) ==";

  (* d = D(ax-1, D(ax-1, D(D(ax-1,ax-1), D(ax-1,ax-1)))), |d| = 10 *)
  let dd = d ax1 ax1 in
  let big = d ax1 (d ax1 (d dd dd)) in
  check "|d| = 10" (Term.size big = 10);

  (* G1 (minimal DAG): p1 -> D(ax-1,ax-1); Start -> D(ax-1,D(ax-1,D(p1,p1))) *)
  let p1_leaf = Term.leaf "p1" in
  let g1 : Grammar.t =
    [
      { Grammar.name = "p1"; arity = 0; rhs = d ax1 ax1 };
      {
        Grammar.name = "Start";
        arity = 0;
        rhs = d ax1 (d ax1 (d p1_leaf p1_leaf));
      };
    ]
  in
  check "|G1| = 8" (Grammar.size g1 = 8);

  (* G2 (parametrised): p1(V1) -> D(ax-1,V1); p2 -> p1(ax-1);
                        Start -> p1(p1(D(p2,p2))) *)
  let p1 a = Term.app "p1" [| a |] in
  let p2 = Term.leaf "p2" in
  let g2 : Grammar.t =
    [
      { Grammar.name = "p1"; arity = 1; rhs = d ax1 pV1 };
      { Grammar.name = "p2"; arity = 0; rhs = p1 ax1 };
      { Grammar.name = "Start"; arity = 0; rhs = p1 (p1 (d p2 p2)) };
    ]
  in
  check "|G2| = 7" (Grammar.size g2 = 7);

  (* val_G(Start) must reproduce the original term d for both grammars *)
  let start_term = Term.leaf "Start" in
  check "val(G1, Start) = d" (Term.equal (Grammar.value g1 start_term) big);
  check "val(G2, Start) = d" (Term.equal (Grammar.value g2 start_term) big);

  (* ref counts (PDNet in-degrees) *)
  check "ref_G2(p1) = 3" (Grammar.ref_count g2 "p1" = 3);
  check "ref_G2(p2) = 2" (Grammar.ref_count g2 "p2" = 2);

  print_endline "== Compression (Example 6 target sizes) ==";

  (* minimal DAG compression of d should match |G1| = 8 *)
  let gdag = Compress.dag_compress [ big ] in
  check "dag_compress |G| = 8" (Grammar.size gdag = 8);
  check "dag value preserved"
    (Term.equal (Grammar.value gdag (Term.leaf "Start")) big);

  (* TreeRePair (parametrised) of d should reach |G2| = 7 *)
  let gtrp = Compress.treerepair [ { Grammar.name = "Start"; arity = 0; rhs = big } ] in
  check "treerepair |G| = 7" (Grammar.size gtrp = 7);
  check "treerepair value preserved"
    (Term.equal (Grammar.value gtrp (Term.leaf "Start")) big);

  Printf.printf "\n%d/%d checks passed\n" (!total - !failures) !total;
  if !failures > 0 then exit 1

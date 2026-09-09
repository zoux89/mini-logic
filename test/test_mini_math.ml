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

  (* (iv) mgt(D(ax-1,D(V1,ax-1))) = (x1 => x2) <- ((x3 => (x4 => x3)) => x2) *)
  check "3(iv) D(ax-1,D(V1,ax-1))"
    (mgt_eq (d ax1 (d pV1 ax1))
       { Formula.head = fv 1 ==> fv 2;
         body = [ (fv 3 ==> (fv 4 ==> fv 3)) ==> fv 2 ] });

  (* (v) mgt(D(D(ax-2,ax-2),ax-2)) is undefined *)
  check "3(v) D(D(ax-2,ax-2),ax-2) undefined" (mgt_undef (d (d ax2 ax2) ax2));

  (* (vi) mgt(D(D(ax-2,V1),ax-2)) = ((x1=>(x2=>x3)) => x4)
           <- ((x1=>(x2=>x3)) => (((x1=>x2)=>(x1=>x3)) => x4)) *)
  check "3(vi) D(D(ax-2,V1),ax-2)"
    (mgt_eq (d (d ax2 pV1) ax2)
       { Formula.head = (fv 1 ==> (fv 2 ==> fv 3)) ==> fv 4;
         body =
           [ (fv 1 ==> (fv 2 ==> fv 3))
             ==> (((fv 1 ==> fv 2) ==> (fv 1 ==> fv 3)) ==> fv 4) ] });

  (* (vii) mgt(D(D(ax-2,ax-1),ax-2)) =
           ((x1=>(x2=>x3)) => (x1=>(x2=>x3))) *)
  check "3(vii) D(D(ax-2,ax-1),ax-2)"
    (mgt_eq (d (d ax2 ax1) ax2)
       {
         Formula.head =
           (fv 1 ==> (fv 2 ==> fv 3)) ==> (fv 1 ==> (fv 2 ==> fv 3));
         body = [];
       });

  print_endline "== Example 5 / Prop. 4 (nonlinear proof terms) ==";

  (* d[V1] = D(V1, D(D(V1,ax-1),ax-1)) is nonlinear. *)
  let d5 = d pV1 (d (d pV1 ax1) ax1) in
  let k = fv 1 ==> (fv 2 ==> fv 1) and k' = fv 3 ==> (fv 4 ==> fv 3) in
  (* A = ((y1=>(y2=>y1)) => (y3=>(y4=>y3))),
     B1 = ((y3=>(y4=>y3)) => ((y1=>(y2=>y1)) => (y3=>(y4=>y3)))) *)
  let a5 = k ==> k' in
  let b5 = k' ==> (k ==> k') in
  check "5 mgt(d[V1]) = A <- B1"
    (mgt_eq d5 { Formula.head = a5; body = [ b5 ] });
  (* A' = mgt(d[ax-1]) = (z1 => (z2 => (z3 => z2))) *)
  let a5' = { Formula.head = fv 1 ==> (fv 2 ==> (fv 3 ==> fv 2)); body = [] } in
  check "5 mgt(d[ax-1]) = A'" (mgt_eq (d ax1 (d (d ax1 ax1) ax1)) a5');
  (* Grammar G = < p(V1) -> d[V1], q -> p(ax-1) >: grammar-mgt(q) = A sigma = A,
     a strict instance of mgt(val_G(q)) = A'. *)
  let g5 : Grammar.t =
    [ { Grammar.name = "p"; arity = 1; rhs = d5 };
      { Grammar.name = "q"; arity = 0; rhs = Term.app "p" [| ax1 |] } ]
  in
  let a5c = { Formula.head = a5; body = [] } in
  (match Kb.grammar_mgts base g5 with
   | None -> check "5 grammar-mgt defined" false
   | Some tbl ->
     let q = Hashtbl.find tbl "q" in
     check "5 grammar-mgt(q) = A" (Formula.alpha_eq_clause q a5c);
     check "5 grammar-mgt(q) >. mgt(val(q)) strictly" (Formula.strict_instance_of q a5'));
  check "5 mgt(val_G(q)) = A'"
    (match Cddc.mgt base (Grammar.value g5 (Term.leaf "q")) with
     | Some c -> Formula.alpha_eq_clause c a5'
     | None -> false);
  check "instance_of A A'" (Formula.instance_of a5c a5');
  check "not instance_of A' A" (not (Formula.instance_of a5' a5c));

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
  let indeg = Pdnet.in_degrees (Pdnet.of_grammar g2) in
  check "PDNet in-degrees of G2"
    (List.assoc "p1" indeg = 3 && List.assoc "p2" indeg = 2
     && List.assoc "Start" indeg = 0);

  print_endline "== Save-value (Sect. 4) ==";

  let prod g n = match Grammar.find g n with Some p -> p | None -> assert false in
  (* linear: closed form ref*(|d|-arity)-|d| *)
  check "sav_G2(p1) = 3*(2-1)-2 = 1" (Grammar.save_value g2 (prod g2 "p1") = 1);
  check "sav_G2(p2) = 2*(1-0)-1 = 1" (Grammar.save_value g2 (prod g2 "p2") = 1);
  check "G2 is linear" (List.for_all Grammar.is_linear g2);
  (* nonlinear: p(V1) -> D(V1,V1); Start -> p(D(ax-1,ax-1)).
     |G| = 2+3 = 5; G' = < Start -> D(D(ax-1,ax-1),D(ax-1,ax-1)) >, |G'| = 6;
     sav = 1 (the linear closed form would give -1). *)
  let gnl : Grammar.t =
    [ { Grammar.name = "p"; arity = 1; rhs = d pV1 pV1 };
      { Grammar.name = "Start"; arity = 0; rhs = Term.app "p" [| d ax1 ax1 |] } ]
  in
  check "|G_nl| = 5" (Grammar.size gnl = 5);
  check "p(V1)->D(V1,V1) is nonlinear" (not (Grammar.is_linear (prod gnl "p")));
  check "sav nonlinear = |G'|-|G| = 1" (Grammar.save_value gnl (prod gnl "p") = 1);
  (* LHS-only parameter (O4): p(V1,V2) -> D(ax-1,V1); Start -> p(ax-1, D(ax-1,ax-1)).
     |G| = 2+4 = 6; G' = < Start -> D(ax-1,ax-1) >, |G'| = 2; sav = -4
     (the closed form would give -2). *)
  let glo : Grammar.t =
    [ { Grammar.name = "p"; arity = 2; rhs = d ax1 pV1 };
      { Grammar.name = "Start"; arity = 0; rhs = Term.app "p" [| ax1; d ax1 ax1 |] } ]
  in
  check "|G_lhsonly| = 6" (Grammar.size glo = 6);
  check "sav LHS-only param = -4" (Grammar.save_value glo (prod glo "p") = -4);
  check "unfold_production preserves val"
    (Term.equal
       (Grammar.value (Grammar.unfold_production glo (prod glo "p")) (Term.leaf "Start"))
       (Grammar.value glo (Term.leaf "Start")));

  print_endline "== KB (Defs. 7, 8) ==";

  (match Kb.grammar_mgts base g2 with
   | None -> check "grammar-mgt(G2) defined" false
   | Some tbl ->
     (* grammar-mgt(Start) = x1 => (x2 => (x3 => (x4 => x3))) *)
     let start_mgt =
       { Formula.head = fv 1 ==> (fv 2 ==> (fv 3 ==> (fv 4 ==> fv 3))); body = [] }
     in
     check "grammar-mgt(Start)" (Formula.alpha_eq_clause (Hashtbl.find tbl "Start") start_mgt);
     check "grammar-mgt(p2) = mgt(D(ax-1,ax-1))"
       (Formula.alpha_eq_clause (Hashtbl.find tbl "p2")
          { Formula.head = fv 1 ==> (fv 2 ==> (fv 3 ==> fv 2)); body = [] });
     let kb = { Kb.base; formulas = Hashtbl.copy tbl; grammar = g2 } in
     check "F = grammar-mgts is a KB" (Kb.is_kb kb);
     check "no strict instances" (Kb.strict_instances kb = []);
     (* F_Start := strict instance (x1 := x5 => x6) *)
     Hashtbl.replace kb.Kb.formulas "Start"
       { Formula.head = (fv 5 ==> fv 6) ==> (fv 2 ==> (fv 3 ==> (fv 4 ==> fv 3))); body = [] };
     check "strict instance still a KB" (Kb.is_kb kb);
     check "strict_instances = [Start]" (Kb.strict_instances kb = [ "Start" ]);
     (* F_p2 := x1 => (x2 => x1), not an instance of grammar-mgt(p2) *)
     Hashtbl.replace kb.Kb.formulas "p2" { Formula.head = fv 1 ==> (fv 2 ==> fv 1); body = [] };
     check "non-instance F breaks KB" (not (Kb.is_kb kb)));
  (* Def. 7: an undefined MGT makes the grammar-MGT undefined *)
  check "grammar-mgt undefined propagates"
    (Kb.grammar_mgts base [ { Grammar.name = "bad"; arity = 0; rhs = d (d ax2 ax2) ax2 } ] = None);

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

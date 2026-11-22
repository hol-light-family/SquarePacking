(* ========================================================================= *)
(* Port of Completion/Cases/C696/AuxUnique.lean (namespace C696Aux).         *)
(* C696 auxiliary bookkeeping: the single-family domains FDomain / GDomain   *)
(* together with distinctness force the unique F / G assignments.  Pure      *)
(* arithmetic on f, g : num -> num.  Tag C696AU_.                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* Lean: Distinct10 *)
let c696au_distinct10 = new_definition
 `c696au_distinct10 (f:num->num) <=>
    forall i. i < 10 ==> forall j. j < 10 ==> ~(i = j) ==> ~(f i = f j)`;;

(* Lean: FDomain *)
let c696au_fdomain = new_definition
 `c696au_fdomain (f:num->num) <=>
    f 0 = 2 /\ f 1 = 0 /\ f 2 = 7 /\ f 3 = 9 /\
    (f 4 = 0 \/ f 4 = 2 \/ f 4 = 4) /\
    (f 5 = 5 \/ f 5 = 7 \/ f 5 = 9) /\
    (f 6 = 0 \/ f 6 = 1) /\
    (f 7 = 2 \/ f 7 = 4 \/ f 7 = 6) /\
    (f 8 = 8 \/ f 8 = 9) /\
    (f 9 = 3 \/ f 9 = 5 \/ f 9 = 7)`;;

(* Lean: GDomain *)
let c696au_gdomain = new_definition
 `c696au_gdomain (g:num->num) <=>
    g 0 = 2 /\ g 1 = 0 /\ g 2 = 7 /\ g 3 = 9 /\
    (g 4 = 0 \/ g 4 = 2 \/ g 4 = 3) /\
    (g 5 = 6 \/ g 5 = 7 \/ g 5 = 9) /\
    (g 6 = 0 \/ g 6 = 1 \/ g 6 = 3) /\
    (g 7 = 2 \/ g 7 = 5) /\
    (g 8 = 6 \/ g 8 = 8 \/ g 8 = 9) /\
    (g 9 = 4 \/ g 9 = 7)`;;

(* Lean: FAssignment *)
let c696au_fassignment = new_definition
 `c696au_fassignment (f:num->num) <=>
    f 0 = 2 /\ f 1 = 0 /\ f 2 = 7 /\ f 3 = 9 /\ f 4 = 4 /\
    f 5 = 5 /\ f 6 = 1 /\ f 7 = 6 /\ f 8 = 8 /\ f 9 = 3`;;

(* Lean: GAssignment *)
let c696au_gassignment = new_definition
 `c696au_gassignment (g:num->num) <=>
    g 0 = 2 /\ g 1 = 0 /\ g 2 = 7 /\ g 3 = 9 /\ g 4 = 3 /\
    g 5 = 6 /\ g 6 = 1 /\ g 7 = 5 /\ g 8 = 8 /\ g 9 = 4`;;

(* the distinctness instances  ~(f i = f j)  for the listed pairs *)
let C696AU_DIST_TAC pairs =
  FIRST_X_ASSUM(fun hs ->
    if not (can (term_match [] `c696au_distinct10 f`) (concl hs)) then failwith "dist" else
    let hs' = REWRITE_RULE[c696au_distinct10] hs in
    MAP_EVERY (fun (i, j) ->
      ASSUME_TAC (REWRITE_RULE[ARITH] (SPEC (mk_small_numeral j)
        (REWRITE_RULE[ARITH] (SPEC (mk_small_numeral i) hs'))))) pairs);;

(* split the domain disjunctions, substitute the values, close by evaluation *)
let C696AU_CASES_TAC =
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && is_numeral (rhs (concl th)) && not (is_numeral (lhs (concl th)))))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH]) THEN
  TRY(FIRST_ASSUM CONTR_TAC) THEN REWRITE_TAC[ARITH];;

(* Lean: f_unique *)
let C696AU_F_UNIQUE = prove
 (`forall f. c696au_fdomain f /\ c696au_distinct10 f ==> c696au_fassignment f`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  C696AU_DIST_TAC [4,1; 4,0; 5,2; 5,3; 6,1; 7,0; 7,4; 8,3; 9,2; 9,5] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `c696au_fdomain f`) (concl th))) THEN
  REWRITE_TAC[c696au_fdomain; c696au_fassignment] THEN C696AU_CASES_TAC);;

(* Lean: g_unique *)
let C696AU_G_UNIQUE = prove
 (`forall g. c696au_gdomain g /\ c696au_distinct10 g ==> c696au_gassignment g`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN DISCH_TAC THEN DISCH_TAC THEN
  C696AU_DIST_TAC [4,1; 4,0; 5,2; 5,3; 6,1; 6,4; 7,0; 8,3; 8,5; 9,2] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `c696au_gdomain f`) (concl th))) THEN
  REWRITE_TAC[c696au_gdomain; c696au_gassignment] THEN C696AU_CASES_TAC);;

(* Lean: unique_assignment *)
let C696AU_UNIQUE_ASSIGNMENT = prove
 (`forall f g. c696au_fdomain f /\ c696au_gdomain g /\ c696au_distinct10 f /\ c696au_distinct10 g
     ==> c696au_fassignment f /\ c696au_gassignment g`,
  MESON_TAC[C696AU_F_UNIQUE; C696AU_G_UNIQUE]);;

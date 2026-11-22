(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976NegativeTop/SeparatingAxes.lean *)
(* (N12Compact.Completion.OtherCases.C976NegativeTop).  The two possible     *)
(* actual square normals.  Lean's N with N.s = -s is (c, s, u, v, a) with    *)
(* s = --t; W is (cW, sW, uW, vW, aW).  upper/lower are ABT_upper/ABT_lower; *)
(* the four-axis split is ABT_FOUR_AXES; the cone and reverse steps of the   *)
(* Lean proof are done directly with ABT_STRICT_BOUNDS.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_Faces.ml";;

let CC976SA_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
         CONV_TAC REAL_RING];;

(* Lean: separating_axes *)
let CC976SA_SEPARATING_AXES = prove
 (`forall c s u v a cW sW uW vW aW t.
     c * c + s * s = &1 /\ &0 < a /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     s = --t /\ &0 < c /\ &0 < t /\ &0 <= cW /\ &0 <= sW /\ a = aW /\
     linside c s u v a (&13 / &50) (&0) /\
     (exists y. y < &0 /\ linside c s u v a (&0) y) /\
     linside cW sW uW vW aW (&0) (&0) /\
     ldisj c s u v a cW sW uW vW aW
     ==> ABT_upper cW sW uW vW aW c s <= ABT_lower c s u v a c s \/
         ABT_upper c s u v a (--sW) cW <= ABT_lower cW sW uW vW aW (--sW) cW`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `y:real` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  let qN = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
  and qW = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] in
  let sb sq (x,y) (nx,ny) =
    MP_TAC(REWRITE_RULE[REAL_POW_2] (SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS)) THEN
    ANTS_TAC THENL [CC976SA_ANTS_TAC; STRIP_TAC] in
  MAP_EVERY (fun d -> sb qN (`&13 / &50`,`&0`) d THEN sb qN (`&0`,`y:real`) d THEN
                      sb qW (`&0`,`&0`) d)
   [(`c:real`,`s:real`); (`--s`,`c:real`); (`cW:real`,`sW:real`); (`--sW`,`cW:real`)] THEN
  MP_TAC(SPECL [`c:real`; `--y`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`sW:real`; `--y`] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL (qN @ qW) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [CC976SA_ANTS_TAC; DISCH_TAC] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  FIRST [RASM_ARITH_TAC; MATCH_MP_TAC(TAUT `false ==> p`) THEN NLIN_TAC ~deg2:false []]);;

(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareTemplate.lean                          *)
(*                                                                           *)
(* The Lean structure Premises A B L R is the hypothesis list of FST_STMT    *)
(* (n12/geometry/fst_stmt.ml); lsquare carries the OpenSquare invariants.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquarePositive.ml";;
needs "n12/geometry/FourSquareBNegativeCorner.ml";;
needs "n12/geometry/fst_stmt.ml";;

(* apply a lemma instance, proving its antecedent from the assumptions and
   transporting the conclusion through the canonical-frame equivalences *)
let FST_STEP th (asl,w as g) =
  let iffs = filter (fun t -> is_forall(concl t) && is_iff(snd(strip_forall(concl t)))) (map snd asl) in
  let ant = lhand(concl th) in
  let ath = TAC_PROOF((asl,ant), REWRITE_TAC[lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN
                       TRY ASM_REAL_ARITH_TAC) in
  ASSUME_TAC (REWRITE_RULE iffs (MP th ath)) g;;

(* Lean: impossible *)
let FST_IMPOSSIBLE = prove
 (FST_STMT,
  REPEAT GEN_TAC THEN REWRITE_TAC[lsquare] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aA:real = aB` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aL` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aB:real = aR` o concl)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `ab:real`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cl:real`; `sl:real`; `ul:real`; `vl:real`; `al:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `al:real = aB` o concl)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `ab:real = aB` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcont; ldisj]) THEN
  ASM_CASES_TAC `&0 <= sb` THENL
   [(* nonnegative canonical B *)
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                `cl:real`; `sl:real`; `ul:real`; `vl:real`; `aB:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] FSP_IMPOSSIBLE) THEN
  REWRITE_TAC[lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    (* negative canonical B *)
    SUBGOAL_THEN `forall x y. ~(linside cB sB uB vB aB x y /\ linside cA sA uA vA aB x y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FST_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] FSAA_POINT) THEN
  FST_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`] FSAF_ROW_POINT) THEN
  FST_STEP(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                  `cl:real`; `sl:real`; `ul:real`; `vl:real`; `aB:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aB:real`] FSBC_NO_LONG_SECTION) THEN
  FST_STEP(SPECL [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                  `cl:real`; `sl:real`; `ul:real`; `vl:real`; `aB:real`;
                  `&1`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
  SUBGOAL_THEN `~linside cB sB uB vB aB (&2) (&5 / &2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cb:real`; `sb:real`; `ub:real`; `vb:real`; `aB:real`;
                `cl:real`; `sl:real`; `ul:real`; `vl:real`; `aB:real`] FSBNC_EXCLUDE) THEN
  REWRITE_TAC[lcont; ldisj] THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

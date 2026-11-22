(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974WallNegativeCaps.lean      *)
(* (N12Compact.Completion.OtherCases.C983.C974MissingCorner).                *)
(* MISSING-CORNER-WALL-SIGN section 1.2.  Conventions of                     *)
(* CP_OtherCases_C983_C974MissingCornerData.ml (Input K W = c974mc_input,    *)
(* unit normal of W explicit).  (Lean header: "Source only, uncompiled".)    *)
(* Tag C974WNC_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974MissingCornerData.ml";;

(* Lean: wall_negative_caps *)
let C974WNC_WALL_NEGATIVE_CAPS = prove
 (`forall cK sK uK vK aK cW sW uW vW aW t.
     cW * cW + sW * sW = &1 /\ c974mc_input cK sK uK vK aK cW sW uW vW aW /\
     sW = --t /\ &0 < cW /\ &0 <= t /\ t <= cW
     ==> &24 / &25 * cW + &6 / &25 * t <= uW /\ &77 * t < &20 * cW /\
         vW + aW <= &2 * t + cW / &2 /\
         (uW + aW <= &2 * cW \/ vW + aW <= &2 * t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cW sW uW vW aW (&24 / &25) (--(&6 / &25))` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c974mc_input; ldisj] o
      check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c974mc_input`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sW = --t`)) THEN
  C974MC_OPEN_TAC THEN
  C974MC_FACT `&1 < aW` C974MC_LIN THEN
  C974MC_FACT `cW <= &1` (NLIN_TAC [SQ_NONNEG `t:real`]) THEN
  C974MC_FACT `uW + aW <= &2 * cW \/ vW + aW <= &2 * t`
    (ASM_CASES_TAC `uW + aW <= &2 * cW` THEN ASM_REWRITE_TAC[] THEN
     C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW (--t) uW vW aW (&2) (&0)`) THEN
  C974MC_FACT `&24 / &25 * cW + &6 / &25 * t <= uW`
    (C974MC_CONTRA THEN
     C974MC_FACT `&24 / &25 * t - &6 / &25 * cW <= vW`
       (C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW (--t) uW vW aW (&24 / &25) (--(&6 / &25))`) THEN
     C974MC_FACT `&27 / &20 * cW - &13 / &20 * t <= uW`
       (C974MC_CONTRA THEN
        C974MC_FACT `vW + aW <= &27 / &20 * t + &13 / &20 * cW`
          (C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW (--t) uW vW aW (&27 / &20) (&13 / &20)`) THEN
        C974MC_FACT `&39 / &100 * t + &89 / &100 * cW < &1`
          (NLIN_TAC [SQ_NONNEG `&39 / &100 * cW - &89 / &100 * t`]) THEN
        C974MC_LIN) THEN
     C974MC_FACT `vW + aW <= &2 * t`
       (FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[] THEN
        C974MC_FACT `cW + t <= &3 / &2` (NLIN_TAC [SQ_NONNEG `cW - t:real`]) THEN
        C974MC_LIN) THEN
     C974MC_FACT `&1 < &26 / &25 * t + &6 / &25 * cW` C974MC_LIN THEN
     NLIN_FACTS_TAC []
      [`&0 <= (cW - t) * (&476 / &625 * cW + &164 / &625 * t)`;
       `&0 < (&26 / &25 * t + &6 / &25 * cW - &1) * (&26 / &25 * t + &6 / &25 * cW + &1)`] THEN
     NLIN_TAC []) THEN
  C974MC_FACT `&77 * t < &20 * cW` C974MC_LIN THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `cW - t / &2 <= uW` THENL
   [ASM_CASES_TAC `uW + aW <= &2 * cW - t / &2` THENL
     [C974MC_LIN;
      C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW (--t) uW vW aW (&2) (&1 / &2)`];
    C974MC_FACT `vW + aW <= t + cW / &2`
      (C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW (--t) uW vW aW (&1) (&1 / &2)`) THEN
    C974MC_LIN]);;

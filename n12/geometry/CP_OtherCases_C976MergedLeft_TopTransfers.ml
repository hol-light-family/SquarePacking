(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976MergedLeft/TopTransfers.lean    *)
(* (namespace N12Compact.Completion.OtherCases.C976MergedLeft).  Literal    *)
(* top advances for the two northeast alternatives.  Lean reflectedTop q =  *)
(* (turnFrame (turnFrame (pullX q))).translated 2 3 is the square           *)
(* (c, --s, 2c + 3s - u - a, v + 2s - 3c, a) (OCC976MLTT_REFLECTED_TOP).     *)
(* C981CompletionShallowCap.negative_cap: C981SC_NEGATIVE_CAP;              *)
(* C981CompletionShallowWall.point: C981SW_POINT; TopOnlyReach.*:           *)
(* OCC976MLTR_*; TopOnlyLeftPoint.point_original: OCTOLP_POINT_ORIGINAL.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_TopOnlyReach.ml";;
needs "n12/geometry/CP_C981_ShallowWall.ml";;

(* Lean: reflectedTop (definition) and reflectedTop_inside *)
let OCC976MLTT_REFLECTED_TOP = prove
 (`forall c s u v a x y.
     linside c (--s) (&2 * c + &3 * s - u - a) (v + &2 * s - &3 * c) a x y <=>
     linside c s u v a (&2 - x) (&3 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let OCC976MLTT_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: mixed_top_advance *)
let OCC976MLTT_MIXED_TOP_ADVANCE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
      cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
      &1 < aN /\ &1 < aW /\ &0 < cN /\ &0 <= sN /\ sN <= cN /\
      linside cN sN uN vN aN (&113 / &50) (&3) /\
      linside cN sN uN vN aN (&2) (&113 / &50) /\
      ~linside cN sN uN vN aN (&113 / &50) (&2) /\
      linside cW sW uW vW aW (&2) (&1543 / &500) /\
      linside cW sW uW vW aW (&8 / &5) (&3) /\
      (forall x y. linside cW sW uW vW aW x y ==> y <= &4) /\
      ldisj cN sN uN vN aN cW sW uW vW aW
      ==> linside cW sW uW vW aW (&127 / &100) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cN:real`; `--sN`; `&2 * cN + &3 * sN - uN - aN`; `vN + &2 * sN - &3 * cN`;
                `aN:real`] C981SC_NEGATIVE_CAP) THEN
  REWRITE_TAC[OCC976MLTT_REFLECTED_TOP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--sW`; `&2 * cW + &3 * sW - uW - aW`; `vW + &2 * sW - &3 * cW`;
                `aW:real`] C981SW_POINT) THEN
  REWRITE_TAC[OCC976MLTT_REFLECTED_TOP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&2 - x`; `&3 + y`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&4`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `ldisj cN sN uN vN aN cW sW uW vW aW` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2 - x`; `&3 + y`]) THEN ASM_SIMP_TAC[]]);;

(* Lean: top_only_advance *)
let OCC976MLTT_TOP_ONLY_ADVANCE = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
      cN * cN + sN * sN = &1 /\ &0 < aN /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
      &1 < aN /\ &1 < aW /\ &0 < cN /\ &0 <= sN /\ sN <= cN /\
      linside cN sN uN vN aN (&47 / &20) (&47 / &20) /\
      linside cN sN uN vN aN (&113 / &50) (&3) /\
      linside cN sN uN vN aN (&101 / &40) (&17 / &8) /\
      ~linside cN sN uN vN aN (&2) (&113 / &50) /\
      ~linside cN sN uN vN aN (&3) (&3) /\
      (forall y. &113 / &50 <= y ==> y <= &64 / &25 ==> ~linside cN sN uN vN aN (&3) y) /\
      linside cW sW uW vW aW (&2) (&3) /\
      (forall x y. linside cW sW uW vW aW x y ==> y <= &4) /\
      ldisj cN sN uN vN aN cW sW uW vW aW
      ==> linside cW sW uW vW aW (&6 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cN sN uN vN aN (&2) (&3)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cN sN uN vN aN cW sW uW vW aW` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&3`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`]
    OCTOLP_POINT_ORIGINAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN - (cN * &2 + sN * &2)`; `vN - (--sN * &2 + cN * &2)`;
                `aN:real`] OCC976MLTR_POSITIVE_TIP) THEN
  REWRITE_TAC[OCC976MLTT_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cW:real`; `--sW`; `&2 * cW + &3 * sW - uW - aW`; `vW + &2 * sW - &3 * cW`;
                `aW:real`] OCC976MLTR_TOP_ONLY_REACH) THEN
  REWRITE_TAC[OCC976MLTT_REFLECTED_TOP] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&2 - x`; `&3 + y`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `&4`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `ldisj cN sN uN vN aN cW sW uW vW aW` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1013 / &500`; `&3`]) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `ldisj cN sN uN vN aN cW sW uW vW aW` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&131 / &50`]) THEN ASM_REWRITE_TAC[]]);;

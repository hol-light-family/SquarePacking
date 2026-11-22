(* ========================================================================= *)
(* Port of Compact/Geometry/MergedLeftCornerSector.lean                      *)
(* (N12Compact.MergedLeftCornerSector).  The lower-left corner points remove *)
(* the steep escape of a merged left central square.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/MergedLeftEscape.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* Lean: corner_point *)
let MLCS_CORNER_POINT = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      u + a <= &2 * (c + s) /\
      v + a <= (&87 / &50) * c - s
      ==> linside c s u v a (&8 / &5) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - s:real`] [`c + s <= &10 / &7`] THEN
  MP_TAC(WFP_SP `&37 / &50` `&3 / &5`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: lower_u *)
let MLCS_LOWER_U = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&2) (&2) /\
      ~linside c s u v a (&1) (&87 / &50) /\
      ~linside c s u v a (&8 / &5) (&1)
      ==> c + (&87 / &50) * s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] MLE_CENTER_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] MLE_LEFT_AUX_FACES) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside c s u v a (&8 / &5) (&1)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MLCS_CORNER_POINT THEN ASM_REWRITE_TAC[]);;

(* Lean: sector *)
let MLCS_SECTOR = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      linside c s u v a (&33 / &20) (&47 / &20) /\
      ~linside c s u v a (&2) (&2) /\
      ~linside c s u v a (&1) (&87 / &50) /\
      ~linside c s u v a (&8 / &5) (&1)
      ==> a <= c + (&13 / &50) * s /\ &0 < s /\ &2331 * s < &1300 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] MLE_CENTER_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] MLCS_LOWER_U) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a <= c + (&13 / &50) * s` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 < (c + &13 / &50 * s - &1) * (c + &13 / &50 * s + &1)`;
    `&0 <= s * (&2331 * s - &1300 * c)`] THEN
  NLIN_TAC ~deg2:false []);;

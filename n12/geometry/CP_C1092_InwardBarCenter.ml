(* ========================================================================= *)
(* Port of Compact/Completion/C1092/InwardBarCenter.lean                      *)
(* (namespace N12Compact.C1092InwardBarCenter).                              *)
(* The half-angle s / (1 + c) is C1092WPS_half (WallProfileScalars);          *)
(* short_projections: WFP_SHORT_PROJECTIONS.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092IBC_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092IBC_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092IBC_LIN_TAC;;

let C1092IBC_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092IBC_MISS_TAC x y; ALL_TAC];;

let C1092IBC_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C1092IBC_LIN_TAC; ALL_TAC]) tms;;

(* the half-angle identities used throughout (from quarter_data) *)
let C1092IBC_HALF = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c * c + s * s = &1
         ==> &0 <= C1092WPS_half c s /\ C1092WPS_half c s <= &1 /\
             C1092WPS_half c s * (&1 + c) = s /\ s * C1092WPS_half c s = &1 - c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `z * (&1 + c) = s` THEN UNDISCH_TAC `(&1 + z * z) * c = &1 - z * z` THEN
  CONV_TAC REAL_RING);;

(* Lean: point *)
let C1092IBC_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\
     linside c s u v a (&0) (&13 / &50) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&14 / &25) (&1) /\
     (forall y. &0 <= y /\ y <= &39 / &100 ==> ~linside c s u v a (&1) y)
     ==> linside c s u v a (&0) (&0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IBC_HALF) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`] [`c <= &1`; `&1 <= c + s`] THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&61 / &100`; `&3 / &5`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                           else REWRITE_RULE[linside] th) THEN
  ASM_CASES_TAC `linside c s u v a (&0) (&0)` THEN ASM_REWRITE_TAC[] THEN
  C1092IBC_FACT_TAC `&0 <= u` `&0` `&0` THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [C1092IBC_LIN_TAC; ALL_TAC] THEN
  C1092IBC_PROD_TAC [`&0 <= (c - s) * ((&41 / &50) * c + (&1 / &50) * s)`] THEN
  SUBGOAL_THEN `s + (&2 / &5) * c <= &1` ASSUME_TAC THENL
   [NLIN_FACTS_TAC [] [`(s + (&2 / &5) * c) * (s + (&2 / &5) * c) <= &49 / &50`] THEN
    NLIN_TAC [SQ_NONNEG `s + (&2 / &5) * c - &1`]; ALL_TAC] THEN
  C1092IBC_FACT_TAC `v + a <= c - (&2 / &5) * s` `&2 / &5` `&1` THEN
  ASM_CASES_TAC `&39 / &100 <= z` THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `&39 / &100`) THEN
    REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    C1092IBC_PROD_TAC [`&0 <= s * (z - &39 / &100)`;
                       `&0 <= (&1 + c) * (z - &39 / &100)`] THEN
    C1092IBC_LIN_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z * c = s - z /\ z * s = &1 - c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092IBC_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v < --z` ASSUME_TAC THENL
   [ASM_CASES_TAC `&3 / &5 <= s + (&2 / &5) * c` THENL
     [C1092IBC_PROD_TAC [`&0 <= z * ((s + (&2 / &5) * c) - &3 / &5)`] THEN
      C1092IBC_LIN_TAC;
      C1092IBC_FACT_TAC `v + a <= c - (&14 / &25) * s` `&14 / &25` `&1` THEN
      C1092IBC_PROD_TAC [`&0 <= z * ((s + (&14 / &25) * c) - &11 / &25)`] THEN
      C1092IBC_LIN_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `z:real` o check (is_forall o concl)) THEN
  REWRITE_TAC[linside] THEN C1092IBC_LIN_TAC);;

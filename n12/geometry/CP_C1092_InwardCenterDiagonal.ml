(* ========================================================================= *)
(* Port of Compact/Completion/C1092/InwardCenterDiagonal.lean                 *)
(* (namespace N12Compact.C1092InwardCenterDiagonal).                         *)
(* canonical_frame: CLF_CANONICAL_FRAME; swap: C1092RC_INSIDE_SWAP;          *)
(* short_projections: WFP_SHORT_PROJECTIONS.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_RigidCharts.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092ICD_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092ICD_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092ICD_LIN_TAC;;

let C1092ICD_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092ICD_MISS_TAC x y; ALL_TAC];;

let C1092ICD_SP dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    TRY(NLIN_TAC []); STRIP_TAC];;

(* Lean: canonical (private) *)
let C1092ICD_CANONICAL = prove
 (`forall c s u v a k.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     ~linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     &7 / &20 <= k /\ k pow 2 <= &151 / &400
     ==> linside c s u v a k k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092ICD_SP `&7 / &10` `--(&7 / &10)` THEN
  C1092ICD_SP `k + &7 / &20` `k - &7 / &20` THEN
  C1092ICD_SP `k - &7 / &20` `k + &7 / &20` THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  C1092ICD_FACT_TAC `c * --(&7 / &20) + s * &7 / &20 <= u` `--(&7 / &20)` `&7 / &20` THEN
  C1092ICD_FACT_TAC `--s * &7 / &20 + c * --(&7 / &20) <= v` `&7 / &20` `--(&7 / &20)` THEN
  SUBGOAL_THEN `&0 <= (k - &7 / &20) * (c + s) /\ &0 <= (k - &7 / &20) * (c - s)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN C1092ICD_LIN_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN C1092ICD_LIN_TAC);;

(* Lean: diagonal *)
let C1092ICD_DIAGONAL = prove
 (`forall c s u v a k.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     ~linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     &7 / &20 <= k /\ k pow 2 <= &151 / &400
     ==> linside c s u v a k k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `linside c' s' u' v' a' k k` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `a':real = a` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ASM_CASES_TAC `s' <= &0` THENL
   [MATCH_MP_TAC C1092ICD_CANONICAL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ONCE_REWRITE_TAC[GSYM C1092RC_INSIDE_SWAP] THEN
    MATCH_MP_TAC C1092ICD_CANONICAL THEN
    ASM_REWRITE_TAC[C1092RC_INSIDE_SWAP] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: point *)
let C1092ICD_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     ~linside c s u v a (&7 / &20) (--(&7 / &20))
     ==> linside c s u v a (&1 / &2) (&1 / &2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C1092ICD_DIAGONAL THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: long_point *)
let C1092ICD_LONG_POINT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (&7 / &20) (&7 / &20) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     ~linside c s u v a (&7 / &20) (--(&7 / &20))
     ==> linside c s u v a (&61 / &100) (&61 / &100)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C1092ICD_DIAGONAL THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

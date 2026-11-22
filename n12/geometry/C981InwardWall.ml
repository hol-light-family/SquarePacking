(* ========================================================================= *)
(* Port of Compact/Geometry/C981InwardWall.lean (Jatloe N12).                 *)
(* A wall owner's inward auxiliary conflicts with its lower singleton point. *)
(* short_projections: WFP_SHORT_PROJECTIONS;                                 *)
(* exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallForcedPoint.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

let C981IW_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* Lean: span_lt_one (private) *)
let C981IW_SPAN_LT_ONE = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1 /\ &37 * s <= &13 * c
         ==> (&89 / &100) * c + (&12 / &25) * s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&13 * c - &37 * s) * (&243107 * c - &318901 * s)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&89 * c + &48 * s - &100) * (&89 * c + &48 * s + &100)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* Lean: positive_impossible (private) *)
let C981IW_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 <= c /\ &0 <= s /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&19 / &25) (&187 / &100)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`c:real`; `s:real`; `&13 / &20`; `&61 / &100`] WFP_SHORT_PROJECTIONS)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  SUBGOAL_THEN `u + a <= c * &33 / &20 + s * &47 / &20` ASSUME_TAC THENL
   [C981IW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--s + c * &87 / &50 <= v` ASSUME_TAC THENL
   [C981IW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&37 * s < &13 * c /\ &9 * c < &35 * s` STRIP_ASSUME_TAC THENL
   [C981IW_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&89 / &100) * c + (&12 / &25) * s < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC C981IW_SPAN_LT_ONE THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C981IW_ARITH_TAC);;

(* Lean: impossible *)
let C981IW_IMPOSSIBLE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     linside c s u v a (&87 / &50) (&2) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&19 / &25) (&187 / &100)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`]
    C981IW_POSITIVE_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;

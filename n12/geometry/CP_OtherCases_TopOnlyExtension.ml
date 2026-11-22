(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/TopOnlyExtension.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.Completion.OtherCases.TopOnlyExtension). *)
(* The top-only outward extension.  canonical_frame is CLF_CANONICAL_FRAME,  *)
(* short_projections is WFP_SHORT_PROJECTIONS; q.translated x y is the       *)
(* 5-tuple (c, s, u - (c x + s y), v - (--s x + c y), a).  The OpenSquare    *)
(* invariants are the explicit hypotheses c * c + s * s = &1 and &0 < a.     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

(* REAL_ARITH over all assumptions built from real relations by ~ /\ \/ ==> *)
let OCTOE_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let OCTOE_SHORT_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC];;

let OCTOE_CU_TAC =
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC];;

(* Lean: positive (private) *)
let OCTOE_POSITIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCTOE_CU_TAC THEN
  OCTOE_SHORT_TAC `&1 / &2` `&37 / &50` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
  OCTOE_ARITH_TAC);;

(* Lean: negative (private) *)
let OCTOE_NEGATIVE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ s <= &0 /\ --s <= c /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
     ~linside c s u v a (&1 / &2) (&0)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN OCTOE_CU_TAC THEN
  OCTOE_SHORT_TAC `&1 / &2` `--(&13 / &50)` THEN
  OCTOE_SHORT_TAC `&1 / &2` `&37 / &50` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
  OCTOE_ARITH_TAC);;

(* Lean: point *)
let OCTOE_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&7 / &20) (&7 / &20) /\ linside c s u v a (&2 / &5) (&1) /\
     ~linside c s u v a (&0) (&13 / &50) /\ ~linside c s u v a (&0) (&1) /\
     ~linside c s u v a (&1 / &2) (&0)
     ==> linside c s u v a (&1 / &2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "linside"
                               with Failure _ -> false)) (concl th)
    then (RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th])
    else failwith "") THEN
  ASM_CASES_TAC `&0 <= s1` THENL
  [MATCH_MP_TAC OCTOE_POSITIVE; MATCH_MP_TAC OCTOE_NEGATIVE] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  UNDISCH_TAC `abs s1 <= c1` THEN RASM_ARITH_TAC);;

(* Lean: S12 inside_translated_iff (helper) *)
let OCTOE_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
     linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
     linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: point_original *)
let OCTOE_POINT_ORIGINAL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&47 / &20) (&47 / &20) /\ linside c s u v a (&12 / &5) (&3) /\
     ~linside c s u v a (&2) (&113 / &50) /\ ~linside c s u v a (&2) (&3) /\
     ~linside c s u v a (&5 / &2) (&2)
     ==> linside c s u v a (&5 / &2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`;
                `a:real`] OCTOE_POINT) THEN
  REWRITE_TAC[OCTOE_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveCentralLeftBand.lean (Jatloe N12).        *)
(* Upper-face consequences in the open positive central sector.              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* REAL_ARITH over all assumptions built from real relations by ~ /\ \/ ==> *)
let PCLB_ARITH_TAC (asl,w as g) =
  let rec ok t = is_real_rel t ||
    (is_neg t && ok (rand t)) ||
    ((is_conj t || is_disj t || is_imp t) && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* Lean: upper_face *)
let PCLB_UPPER_FACE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ u + a <= &2 * (c + s) /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     linside c s u v a (&3 / &2) (&2) /\
     ~linside c s u v a (&1) (&2)
     ==> v + a <= &2 * c - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  PCLB_ARITH_TAC);;

(* Lean: northwest_cap *)
let PCLB_NORTHWEST_CAP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&3 / &2) (&2) /\
     linside c s u v a (&2) (&3 / &2) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&1) (&8 / &5)
     ==> v + a <= (&47 / &20) * c - (&33 / &20) * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&13 / &20) * c + (&3 / &4) * s < &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `c - &13 / &20`; SQ_NONNEG `s - &3 / &4`]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  PCLB_ARITH_TAC);;

(* Lean: left_point_tilt *)
let PCLB_LEFT_POINT_TILT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     v + a <= (&47 / &20) * c - (&33 / &20) * s /\
     linside c s u v a (&1) (&2)
     ==> &13 * s < &7 * c`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

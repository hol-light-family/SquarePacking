(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallSmallOffset.lean                      *)
(* Normal is c977cc_normal.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/FullAuxWallRightMargin.ml";;
needs "n12/geometry/FullAuxWallRightSupport.ml";;

(* Lean: cosine *)
let FAWSO_COSINE = prove
 (`forall C S. c977cc_normal C S /\ &25 * S <= &9 * C ==> &47 / &50 < C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal C S` THEN REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  NLIN_FACTS_TAC [] [`&0 <= (&9 * C - &25 * S) * (&9 * C + &25 * S)`] THEN
  NLIN_TAC []);;

(* Lean: offset *)
let FAWSO_OFFSET = prove
 (`forall c s C S e u. c977cc_normal c s /\ c977cc_normal C S /\ &4 * s <= c /\
     &25 * S <= &9 * C /\ e < &1 / &1250 /\ (c * C + s * S) * u <= e
     ==> u < &1 / &1000`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FAWRM_CENTRAL_BOUNDS) THEN
  MP_TAC(SPECL [`C:real`; `S:real`] FAWSO_COSINE) THEN
  MP_TAC(SPECL [`C:real`; `S:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  NLIN_FACTS_TAC [] [`&0 <= (c - &24 / &25) * C`; `&0 <= s * S`; `&564 / &625 <= c * C + s * S`] THEN
  NLIN_TAC []);;

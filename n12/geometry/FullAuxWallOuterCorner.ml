(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallOuterCorner.lean                      *)
(* Normal is c977cc_normal.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FullAuxWallEscape.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: corner_cap *)
let FAWOC_CORNER_CAP = prove
 (`forall c s u v a.
     c977cc_normal c s /\ &1 < a /\ u + a <= (&8 / &5) * c + &3 * s /\
     linside c s u v a (&33 / &20) (&47 / &20) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&3)
     ==> v + a <= &3 * c - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&33 / &20) (&47 / &20)`; `linside c s u v a (&1) (&12 / &5)`] THEN
  MP_TAC(ASSUME `~linside c s u v a (&1) (&3)`) THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* Lean: two_caps_marker *)
let FAWOC_TWO_CAPS_MARKER = prove
 (`forall c s u v a.
     c977cc_normal c s /\ s < &3 / &10 /\ &1 < a /\
     u + a <= (&8 / &5) * c + &3 * s /\ v + a <= &3 * c - s /\
     linside c s u v a (&33 / &20) (&47 / &20) /\ linside c s u v a (&1) (&113 / &50)
     ==> linside c s u v a (&457 / &500) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&33 / &20) (&47 / &20)`; `linside c s u v a (&1) (&113 / &50)`] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

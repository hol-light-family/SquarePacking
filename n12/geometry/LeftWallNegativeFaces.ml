(* ========================================================================= *)
(* Port of Compact/Geometry/LeftWallNegativeFaces.lean                       *)
(*                                                                           *)
(* The wall square W = (c, s, u, v, a) with s = --t; Normal is c977cc_normal;*)
(* negative_bands is C977NCO_NEGATIVE_BANDS.                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;

(* Lean: faces *)
let LWNF_FACES = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ s = --t /\ c977cc_normal c t /\ &1 < a /\
     lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&113 / &50) /\
     ~linside c s u v a (&1) (&2) /\
     ~linside c s u v a (&457 / &500) (&3)
     ==> u + a <= c - &2 * t /\
         v + a <= (&457 / &500) * t + &3 * c /\
         a * (c + t) <= c * (u + a) + t * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal; REAL_ABS_NEG]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  SUBGOAL_THEN `abs t = t` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c (--t) u v a (&457 / &500) (&2)`; `linside c (--t) u v a (&1) (&113 / &50)`] THEN
  SUBGOAL_THEN `u + a <= c - &2 * t` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c (--t) u v a (&1) (&2)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&457 / &500) * t + &3 * c` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c (--t) u v a (&457 / &500) (&3)`) THEN REWRITE_TAC[linside] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: far_margin (private) *)
let LWNF_FAR_MARGIN = prove
 (`forall d t. c977cc_normal d t
     ==> &0 < d + t - (&113 / &100) * d * t - &19 / &25 - (&77 / &500) * t pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `d - t:real`]
   [`&0 <= d * t`; `&0 <= (d + t - &1) * (&10 / &7 - (d + t))`;
    `&1 + (&14 / &17) * d * t <= d + t`; `d * t <= &1 / &2`;
    `&0 <= (d - t) * (d + t)`; `t pow 2 <= &1 / &2`] THEN
  NLIN_TAC []);;

(* Lean: lower_face_and_tilt *)
let LWNF_LOWER_FACE_AND_TILT = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ s = --t /\ c977cc_normal c t /\ &1 < a /\
     lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&113 / &50) /\
     ~linside c s u v a (&1) (&2) /\
     ~linside c s u v a (&457 / &500) (&3) /\
     ~linside c s u v a (&19 / &25) (&187 / &100)
     ==> (&19 / &25) * t + (&187 / &100) * c <= v /\ t < &3 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`] LWNF_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LWNF_FAR_MARGIN) THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `s = --t` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c977cc_normal]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_conj(concl th) && is_real_rel(lhand(concl th))
    then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c (--t) u v a (&457 / &500) (&2)`; `linside c (--t) u v a (&1) (&113 / &50)`] THEN
  NLIN_FACTS_TAC []
   [`&0 <= t * ((&457 / &500) * t + &3 * c - (v + a))`;
    `&0 < (a - &1) * (c + t)`;
    `&0 < c * (u + a - ((&19 / &25) * c - (&187 / &100) * t))`;
    `(&19 / &25) * c - (&187 / &100) * t < u + a`] THEN
  SUBGOAL_THEN `(&19 / &25) * t + (&187 / &100) * c <= v` ASSUME_TAC THENL
   [MP_TAC(ASSUME `~linside c (--t) u v a (&19 / &25) (&187 / &100)`) THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `&3 * c - &4 * t`; SQ_NONNEG `(&4 / &5) * c + (&3 / &5) * t - &1`]
   [`((&4 / &5) * c + (&3 / &5) * t) pow 2 <= &1`; `(&4 / &5) * c + (&3 / &5) * t <= &1`] THEN
  RASM_ARITH_TAC);;

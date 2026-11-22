(* ========================================================================= *)
(* Port of Compact/Completion/C981/CentralPositivePoint.lean                  *)
(* (N12Compact.C981CompletionCentralPositivePoint).  The whole left-wall     *)
(* segment forces a positive central square to own (2, 131/50).              *)
(* inside_segment is CES_INSIDE_SEGMENT; short_projections is                *)
(* WFP_SHORT_PROJECTIONS; affine_endpoint_nonnegative is                     *)
(* SCAP_AFFINE_ENDPOINT_NONNEG; the rotated-box point is TSS_INSIDE_FACE.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_HalfAngle.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C981CPP_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

let C981CPP_FACE t face =
  SUBGOAL_THEN face ASSUME_TAC THENL
  [UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC];;

let C981CPP_POS_OF_MUL = prove
 (`forall k y. &0 <= k /\ &0 < k * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * --y` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: scalar (private) *)
let C981CPP_SCALAR = prove
 (`forall c s. &0 <= c /\ &0 < s /\ s <= c /\ c pow 2 + s pow 2 = &1
         ==> (&97 / &100) * c * s < c + s - &1 + (&7 / &20) * s pow 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C981HA_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`c981ha_half c s`,`t:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &3 / &100 - (&3 / &10) * t + (&197 / &100) * t pow 2 - t pow 3`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 / &2 - t) * (t * t)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
   MP_TAC(SPEC `t - &5 / &49` REAL_LE_SQUARE) THEN
   REWRITE_TAC[REAL_POW_2; REAL_ARITH `t pow 3 = t * t * t`] THEN REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + t pow 2) pow 2 * (c + s - &1 + (&7 / &20) * s pow 2 - (&97 / &100) * c * s) =
    &2 * t * (&3 / &100 - (&3 / &10) * t + (&197 / &100) * t pow 2 - t pow 3)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `(&1 + t pow 2) * c = &1 - t pow 2` THEN
   UNDISCH_TAC `(&1 + t pow 2) * s = &2 * t` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < y - x ==> x < y`) THEN
  MATCH_MP_TAC C981CPP_POS_OF_MUL THEN EXISTS_TAC `(&1 + t pow 2) pow 2` THEN
  REWRITE_TAC[REAL_LE_POW_2] THEN
  SUBGOAL_THEN `&0 < (&2 * t) *
     (&3 / &100 - (&3 / &10) * t + (&197 / &100) * t pow 2 - t pow 3)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC
   `(&1 + t pow 2) pow 2 * (c + s - &1 + (&7 / &20) * s pow 2 - (&97 / &100) * c * s) =
    &2 * t * (&3 / &100 - (&3 / &10) * t + (&197 / &100) * t pow 2 - t pow 3)` THEN
  REAL_ARITH_TAC);;

(* Lean: left_support (private) *)
let C981CPP_LEFT_SUPPORT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
     linside c s u v a (&2) (&2) /\ (forall y. ~linside c s u v a (&1) y)
     ==> &1 <= c * u - s * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall x y. linside c s u v a x y ==> &1 <= x` ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `exists t. t * (&2 - x) = &1 - x` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(&1 - x) / (&2 - x)` THEN UNDISCH_TAC `x < &1` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= t /\ t <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `x:real`; `y:real`;
                 `&2`; `&2`; `t:real`] CES_INSIDE_SEGMENT) THEN
   ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `(&1 - t) * x + t * &2 = &1` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= c * u - s * (v + a) - &1 ==> &1 <= c * u - s * (v + a)`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c + s:real`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + e) - s * (v + a - e)`;
                                `s * (u + e) + c * (v + a - e)`]) THEN
  ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN ANTS_TAC THENL
  [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: point *)
let C981CPP_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&2) (&2) /\ linside c s u v a (&3 / &2) (&2) /\
     linside c s u v a (&2) (&5 / &2) /\ linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&47 / &20) /\
     (forall y. &113 / &50 <= y /\ y <= &14 / &5 ==> ~linside c s u v a (&1) y)
     ==> linside c s u v a (&2) (&131 / &50)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c <= &1` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`]; ALL_TAC] THEN
  MAP_EVERY (fun (x,y) ->
    MP_TAC(SPECL [`c:real`; `s:real`; x; y] WFP_SHORT_PROJECTIONS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC)
   [`&7 / &10`,`&7 / &10`; `--(&13 / &20)`,`&61 / &100`] THEN
  C981CPP_UNFOLD_TAC `linside c s u v a (&2) (&2)` THEN
  C981CPP_UNFOLD_TAC `linside c s u v a (&3 / &2) (&2)` THEN
  C981CPP_UNFOLD_TAC `linside c s u v a (&2) (&5 / &2)` THEN
  C981CPP_UNFOLD_TAC `linside c s u v a (&33 / &20) (&47 / &20)` THEN
  C981CPP_FACE `~linside c s u v a (&47 / &20) (&47 / &20)` `u + a <= (&47 / &20) * (c + s)` THEN
  C981CPP_FACE `~linside c s u v a (&33 / &20) (&33 / &20)`
    `--(&33 / &20) * s + (&33 / &20) * c <= v` THEN
  SUBGOAL_THEN `&2 * c + (&131 / &50) * s < u + a` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `c + (&113 / &50) * s <= u` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&113 / &50` o check (is_forall o concl)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `v + a <= --s + (&14 / &5) * c` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&14 / &5` o check (is_forall o concl)) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `forall y. ~linside c s u v a (&1) y` ASSUME_TAC THENL
   [X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&113 / &50 <= y /\ y <= &14 / &5` STRIP_ASSUME_TAC THENL
    [UNDISCH_TAC `linside c s u v a (&1) y` THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 < y - x ==> x <= y`) THEN
      MATCH_MP_TAC C981CPP_POS_OF_MUL THEN EXISTS_TAC `s:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; RASM_ARITH_TAC];
      MATCH_MP_TAC(REAL_ARITH `&0 < x - y ==> y <= x`) THEN
      MATCH_MP_TAC C981CPP_POS_OF_MUL THEN EXISTS_TAC `c:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; RASM_ARITH_TAC]]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `&14 / &5`)) (concl th))) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C981CPP_LEFT_SUPPORT) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`] C981CPP_SCALAR) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN `&0 <= c * ((&2 * c + (&131 / &50) * s) - (u + a)) /\
                 &0 <= s * (v - (--(&33 / &20) * s + (&33 / &20) * c)) /\
                 &0 < (a - &1) * (c + s)` MP_TAC THENL
   [REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

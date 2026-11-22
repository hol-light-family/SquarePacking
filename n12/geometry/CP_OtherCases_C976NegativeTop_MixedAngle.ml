(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976NegativeTop/MixedAngle.lean     *)
(* (N12Compact.Completion.OtherCases.C976NegativeTop).  Lean's square N with *)
(* N.s = -s is (c, s, u, v, a) with s = --t (Lean's parameter s is t here). *)
(* CanonicalScalars.bounds: CCCS_BOUNDS; OutwardScalars.increasing_          *)
(* projection: CCOS_INCREASING_PROJECTION; CanonicalProjection.before:       *)
(* CCCP_BEFORE; LowerCornerSupport.horizontal: OCLCS_HORIZONTAL; turnFrame   *)
(* and turnFrame_inside: CCBBS_TURN_INSIDE (BottomBarSupport port).          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_CommonCases_OutwardScalars.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/CP_OtherCases_LowerCornerSupport.ml";;
needs "n12/geometry/CP_OtherCases_BottomBarSupport.ml";;

let CC976MA_MISSING_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

let CC976MA_SEG_TAC x =
  FIRST_ASSUM(MP_TAC o SPEC x o check (is_forall o concl)) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC;;

(* Lean: mixed_angle *)
let CC976MA_MIXED_ANGLE = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
     linside c s u v a (&7 / &20) (--(&13 / &20)) /\
     linside c s u v a (&0) (--(&37 / &50)) /\
     linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&0) (&0) /\
     (forall x. &13 / &50 <= x /\ x <= &1 / &2 ==> ~linside c s u v a x (--(&1)))
     ==> &0 < t /\ t < (&13 / &25) * c /\ &0 <= u /\ (&1 / &2) * t - c <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  SUBGOAL_THEN `c pow 2 + t pow 2 = &1` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c (--t) u v a (&7 / &20) (--(&13 / &20))`;
    `linside c (--t) u v a (&0) (--(&37 / &50))`;
    `linside c (--t) u v a (&13 / &50) (&0)`] THEN
  SUBGOAL_THEN `&0 <= u` ASSUME_TAC THENL
  [CC976MA_MISSING_TAC `~linside c (--t) u v a (&0) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `&13 / &50`; `&1`] CCOS_INCREASING_PROJECTION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  SUBGOAL_THEN `(&13 / &50) * t - c <= v` ASSUME_TAC THENL
  [CC976MA_SEG_TAC `&13 / &50`; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &2) * t - c <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `u + a <= (&1 / &2) * c + t` ASSUME_TAC THENL
   [CC976MA_SEG_TAC `&1 / &2`; ALL_TAC] THEN
   SUBGOAL_THEN `(&3 / &4) * c < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `t:real`; `&4 / &5`; `&3 / &5`; `&1 / &2`; `&1`] CCCP_BEFORE) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
     RASM_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `&3 / &5 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`&4 / &5 - c`; `&4 / &5 + c`] REAL_LT_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`&3 / &5 - t`; `&3 / &5 + t`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
    NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   SUBGOAL_THEN `t < &1` ASSUME_TAC THENL [NLIN_TAC []; ALL_TAC] THEN
   MP_TAC(PURE_REWRITE_RULE[REAL_NEG_NEG] (PURE_REWRITE_RULE[CCBBS_TURN_INSIDE]
     (SPECL [`--(--t)`; `c:real`; `v:real`; `--u - a`; `a:real`; `&13 / &50`; `&1 / &2`]
     OCLCS_HORIZONTAL))) THEN
   ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN
    FIRST [RASM_ARITH_TAC;
           UNDISCH_TAC `c * c + --t * --t = &1` THEN CONV_TAC REAL_RING;
           GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
           ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
   MP_TAC(SPECL [`&1 - t`; `(&37 / &50) * t - &13 / &50`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(SPECL [`t:real`; `u + a - &1`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   MP_TAC(SPECL [`c:real`; `--(&37 / &50) * c - v`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC] THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

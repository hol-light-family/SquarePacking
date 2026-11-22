(* ========================================================================= *)
(* Port of Compact/Geometry/WallSignChord.lean (N12Compact.WallSignChord).   *)
(* Theorem 1 of C1092-WALL-SIGN-CHORD: one left wall, one marker, one        *)
(* omitted central marker and the closed center sign force the whole chord.  *)
(* centerX/centerY are lcx/lcy; exists_positive_frame is                     *)
(* WCB_EXISTS_POSITIVE_FRAME; affine_endpoint_nonnegative is                 *)
(* SCAP_AFFINE_ENDPOINT_NONNEG.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallSignChordPositive.ml";;
needs "n12/geometry/WallSignChordNegative.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/geometry/SectionCapacity.ml";;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let WSC_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_left_wall (private) *)
let WSC_POSITIVE_LEFT_WALL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      (forall x y. linside c s u v a x y ==> --(&1) <= x)
      ==> a * (c + s) / &2 - &1 <= lcx c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &1 + c * u - s * (v + a)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`a:real`; `c + s`] THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`c * (u + t) - s * (v + a - t)`; `s * (u + t) + c * (v + a - t)`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[linside] THEN
      SUBGOAL_THEN
       `c * (c * (u + t) - s * (v + a - t)) + s * (s * (u + t) + c * (v + a - t)) =
        u + t /\
        --s * (c * (u + t) - s * (v + a - t)) + c * (s * (u + t) + c * (v + a - t)) =
        v + a - t` (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
        ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    REWRITE_TAC[lcx] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: local_point *)
let WSC_LOCAL_POINT = prove
 (`forall c s u v a r.
      c * c + s * s = &1 /\ &1 < a /\
      (forall x y. linside c s u v a x y ==> --(&1) <= x) /\
      linside c s u v a (--(&43 / &500)) (&0) /\
      ~linside c s u v a (&13 / &20) (&7 / &20) /\
      &0 <= lcy c s u v a /\
      &11 / &50 <= r /\ r <= &39 / &100
      ==> linside c s u v a (&0) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) then
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
      else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM(ASSUME `lcx c1 s1 u1 v1 a = lcx c s u v a`);
                              GSYM(ASSUME `lcy c1 s1 u1 v1 a = lcy c s u v a`)]) THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`]
    WSC_POSITIVE_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ASM_CASES_TAC `s1 <= c1` THENL
   [MATCH_MP_TAC WSCP_POSITIVE_POINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `forall x y. linside s1 (--c1) (--v1 - a) u1 a x y <=> linside c1 s1 u1 v1 a x y`
    (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] THEN
               ASSUME_TAC th) THENL
   [REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lcx s1 (--c1) (--v1 - a) u1 a = lcx c1 s1 u1 v1 a /\
                lcy s1 (--c1) (--v1 - a) u1 a = lcy c1 s1 u1 v1 a`
    STRIP_ASSUME_TAC THENL [REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC WSCN_NEGATIVE_POINT THEN EXISTS_TAC `c1:real` THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: chord *)
let WSC_CHORD = prove
 (`forall c s u v a r.
      c * c + s * s = &1 /\ &1 < a /\
      (forall x y. linside c s u v a x y ==> &0 <= x) /\
      linside c s u v a (&457 / &500) (&2) /\
      ~linside c s u v a (&33 / &20) (&47 / &20) /\
      &2 <= lcy c s u v a /\
      &111 / &50 <= r /\ r <= &239 / &100
      ==> linside c s u v a (&1) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &1 + s * &2)`;
                `v - (--s * &1 + c * &2)`; `a:real`; `r - &2`] WSC_LOCAL_POINT) THEN
  REWRITE_TAC[WSC_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[REAL_ARITH `&2 + r - &2 = r`] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&1 + x`; `&2 + y`]) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[lcy] THEN UNDISCH_TAC `&2 <= lcy c s u v a` THEN
    REWRITE_TAC[lcy] THEN UNDISCH_TAC `c * c + s * s = &1` THEN
    CONV_TAC REAL_ARITH;
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

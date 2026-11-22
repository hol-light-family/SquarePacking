(* ========================================================================= *)
(* Port of Compact/Geometry/C982Merged.lean (N12Compact.C982Merged).         *)
(* The merged bottom owner in C982 has a forced negative angle and reaches   *)
(* the endpoint of the obstructing segment.                                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/FourSquareAForced.ml";;

let C982M_LIN_TAC =
  REPEAT(FIRST_X_ASSUM(fun th ->
    if is_forall(concl th) then ALL_TAC else NO_TAC)) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  REWRITE_TAC[linside; lclosed; REAL_ABS_BOUNDS] THEN REAL_ARITH_TAC;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean), with the     *)
(* translated square written out as a 5-tuple.                               *)
let C982M_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: positive_impossible (private) *)
let C982M_POSITIVE_IMPOSSIBLE = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\ &0 < c /\ &0 <= s /\ s <= c /\
      linside c s u v a (&0) (--(&543 / &500)) /\
      linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
      ~linside c s u v a (--(&13 / &50)) (--(&1)) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20))
      ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FSAF_SP_TAC `&61 / &100` `&13 / &20` THEN
  C982M_LIN_TAC);;

(* Lean: negative_faces *)
let C982M_NEGATIVE_FACES = prove
 (`forall c s u v a t.
      c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
      linside c s u v a (&0) (--(&543 / &500)) /\
      linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
      ~linside c s u v a (--(&13 / &50)) (--(&1)) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20))
      ==> --(&13 / &50) * t - c <= v /\
          u + a <= &7 / &20 * (c + t) /\
          &43 * c < &130 * t /\ &368 * t < &175 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FSAF_SP_TAC `&61 / &100` `&13 / &20` THEN
  SUBGOAL_THEN `--(&13 / &50) * t - c <= v` ASSUME_TAC THENL
   [UNDISCH_THEN `~linside c s u v a (&7 / &20) (--(&7 / &20))` (K ALL_TAC) THEN
    C982M_LIN_TAC;
    ALL_TAC] THEN
  C982M_LIN_TAC);;

(* Lean: endpoint_span (private) *)
let C982M_ENDPOINT_SPAN = prove
 (`forall c t. &0 <= c /\ &0 <= t /\ c pow 2 + t pow 2 = &1 /\ &368 * t <= &175 * c
         ==> &21 / &25 * c + &14 / &25 * t < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&175 * c - &368 * t) * (&173509 * c - &193060 * t)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&21 * c + &14 * t - &25) * (&21 * c + &14 * t + &25)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_reach (private) *)
let C982M_NEGATIVE_REACH = prove
 (`forall c s u v a t.
      c * c + s * s = &1 /\ s = --t /\ &1 < a /\ &0 < c /\ &0 <= t /\ t <= c /\
      linside c s u v a (&0) (--(&543 / &500)) /\
      linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
      ~linside c s u v a (--(&13 / &50)) (--(&1)) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20))
      ==> linside c s u v a (&3 / &10) (--(&4 / &25))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`]
    C982M_NEGATIVE_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C982M_ENDPOINT_SPAN) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN ASM_REWRITE_TAC[REAL_POW_2] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  FSAF_SP_TAC `&1 / &20` `--(&19 / &100)` THEN
  UNDISCH_THEN `~linside c s u v a (--(&13 / &50)) (--(&1))` (K ALL_TAC) THEN
  UNDISCH_THEN `~linside c s u v a (&7 / &20) (--(&7 / &20))` (K ALL_TAC) THEN
  C982M_LIN_TAC);;

(* Lean: reaches *)
let C982M_REACHES = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&0) (--(&543 / &500)) /\
      linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
      ~linside c s u v a (--(&13 / &50)) (--(&1)) /\
      ~linside c s u v a (&7 / &20) (--(&7 / &20))
      ==> linside c s u v a (&3 / &10) (--(&4 / &25))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = a`)) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) then
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th]
      else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s1` THENL
   [MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC C982M_POSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C982M_NEGATIVE_REACH THEN EXISTS_TAC `--s1` THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: reaches_original *)
let C982M_REACHES_ORIGINAL = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &1 < a /\
      linside c s u v a (&2) (&457 / &500) /\
      linside c s u v a (&33 / &20) (&33 / &20) /\
      ~linside c s u v a (&87 / &50) (&1) /\
      ~linside c s u v a (&47 / &20) (&33 / &20)
      ==> linside c s u v a (&23 / &10) (&46 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u - (c * &2 + s * &2)`;
                `v - (--s * &2 + c * &2)`; `a:real`] C982M_REACHES) THEN
  REWRITE_TAC[C982M_INSIDE_TRANSLATED] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[]);;

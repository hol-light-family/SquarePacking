(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976NegativeTop/Main.lean           *)
(* (N12Compact.Completion.OtherCases.C976NegativeTop).  The continuous       *)
(* two-square Theorem 1 of C976-NEGATIVE-NE-TOP-ENDING.md about the actual   *)
(* northeast square N and top square W.  N is c s u v a with N.s = --t       *)
(* (Lean's s is t here), W is cW sW uW vW aW; unit normals / positive sides   *)
(* are explicit hypotheses.  Alternative = cc976f_alternative; faces =       *)
(* CC976F_FACES; alternative_anchor = CC976F_ALTERNATIVE_ANCHOR;             *)
(* separating_axes = CC976SA_SEPARATING_AXES; left_face = CC976LF_LEFT_FACE; *)
(* WallProfile.downward_upper / upper_in_bands / vertex = OCWPSG_DOWNWARD_   *)
(* UPPER / OCWPSG_UPPER_IN_BANDS / OCWPVG_VERTEX; northeast_margin =         *)
(* C976NTNE_NORTHEAST_MARGIN; top_outer/mixed/negative_margin =              *)
(* C976NTT_TOP_*_MARGIN; ownU / ownV = ABT_OWNU / ABT_OWNV; ClosedInside =   *)
(* lclosed.  Lean `let` abbreviations d, k, D are written out.  Tag C976NTM_. *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_LeftFace.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_NortheastScalars.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_TopScalars.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_SeparatingAxes.ml";;
needs "n12/geometry/CP_OtherCases_C976NegativeTop_Faces.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/ABTransverse.ml";;

let C976NTM_LIN = NLIN_TAC ~deg2:false [];;

let C976NTM_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; C976NTM_LIN]; ALL_TAC];;

let C976NTM_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C976NTM_LIN; ALL_TAC];;

let C976NTM_RING tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
     type_of(lhs(concl th)) = `:real`))) THEN CONV_TAC REAL_RING; ALL_TAC];;

let C976NTM_MAXMIN = prove
 (`forall x. max x (&0) = x - min x (&0)`,
  GEN_TAC THEN REWRITE_TAC[real_max; real_min] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let C976NTM_ABS_MAX = prove
 (`forall x. abs x = &2 * max x (&0) - x`,
  GEN_TAC THEN REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: supportW (local fact of contrary_impossible) *)
let C976NTM_SUPPORT_W = prove
 (`forall cW sW uW vW aW c t.
     &0 <= cW /\ &0 <= sW /\ &0 <= c /\ &0 <= t
     ==> ABT_upper cW sW uW vW aW c (--t) =
         (c * cW - t * sW) * (uW + aW) - (c * sW + t * cW) * vW -
         aW * min (c * cW - t * sW) (&0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[OCWPSG_DOWNWARD_UPPER; C976NTM_MAXMIN] THEN
  REAL_ARITH_TAC);;

(* Lean: supportN (local fact of contrary_impossible) *)
let C976NTM_SUPPORT_N = prove
 (`forall c t u v a cW sW.
     &0 < c * sW + t * cW
     ==> ABT_upper c (--t) u v a (--sW) cW =
         --(c * sW + t * cW) * u + (c * cW - t * sW) * v + a * max (c * cW - t * sW) (&0)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[OCWPSG_UPPER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `--sW * c + cW * --t = --(c * sW + t * cW)`;
              REAL_ARITH `-- --sW * --t + cW * c = c * cW - t * sW`; REAL_ABS_NEG] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
  REWRITE_TAC[C976NTM_ABS_MAX] THEN REAL_ARITH_TAC);;
(* Lean: contrary_impossible (private) *)
let C976NTM_CONTRARY_IMPOSSIBLE = prove
 (`forall c s u v a cW sW uW vW aW t.
     c * c + s * s = &1 /\ &0 < a /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     s = --t /\ &1 < a /\ a = aW /\ &0 < c /\ &0 < t /\ t <= c /\
     &0 < cW /\ &0 <= sW /\ (&2 / &3) * sW <= cW /\
     linside c s u v a (&7 / &20) (--(&13 / &20)) /\ linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1) (--(&11 / &25)) /\ cc976f_alternative c s u v a /\
     linside cW sW uW vW aW (&0) (&0) /\ ~linside cW sW uW vW aW (--(&18 / &25)) (&0) /\
     sW * (uW + aW) + cW * (vW + aW) <= &1 /\
     ldisj c s u v a cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `~linside c s u v a (&0) (&0)` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj c s u v a cW sW uW vW aW` THEN REWRITE_TAC[ldisj] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`] CC976F_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CC976F_ALTERNATIVE_ANCHOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    CC976SA_SEPARATING_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C976NTM_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    CC976LF_LEFT_FACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[cc976f_faces] o
    check (fun th -> can (term_match [] `cc976f_faces c s u v a t`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aW`)) THEN
  C976NTM_RING `c pow 2 + t pow 2 = &1` THEN
  C976NTM_RING `cW pow 2 + sW pow 2 = &1` THEN
  C976NTM_PROD `&0 <= c * sW` THEN C976NTM_PROD `&0 < t * cW` THEN
  C976NTM_FACT `&0 < c * sW + t * cW` THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`; `c:real`; `t:real`]
    C976NTM_SUPPORT_W) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C976NTM_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `u:real`; `v:real`; `a:real`; `cW:real`; `sW:real`]
    C976NTM_SUPPORT_N) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `a:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  C976NTM_FACT `a - (&18 / &25) * cW <= uW + a` THEN
  C976NTM_FACT `cW * vW <= &1 - sW * (uW + a) - cW * a` THEN
  C976NTM_PROD `&0 <= sW * ((uW + a) - (a - (&18 / &25) * cW))` THEN
  C976NTM_FACT `cW * vW <= &1 - a * (cW + sW) + (&18 / &25) * cW * sW` THEN
  ABBREV_TAC `eta = (&1 - sW) / cW` THEN
  SUBGOAL_THEN `cW * eta = &1 - sW` ASSUME_TAC THENL
   [EXPAND_TAC "eta" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C976NTM_LIN; ALL_TAC] THEN
  C976NTM_PROD `&0 < (a - &1) * cW` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `ABT_upper`)) (concl th))) THENL
   [(* northAxis *)
    UNDISCH_TAC `ABT_upper cW sW uW vW a c (--t) <= ABT_lower c (--t) u v a c (--t)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c:real`; `t:real`; `cW:real`; `sW:real`] C976NTNE_NORTHEAST_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C976NTM_LIN; ASM_REWRITE_TAC[]] THEN
    DISCH_TAC THEN
    ABBREV_TAC `mn = min (c * cW - t * sW) (&0)` THEN
    SUBGOAL_THEN `mn <= &0` ASSUME_TAC THENL [EXPAND_TAC "mn" THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C976NTM_PROD `&0 <= cW * (u - ((c * cW - t * sW) * (uW + a) - (c * sW + t * cW) * vW - a * mn))` THEN
    C976NTM_PROD `&0 <= (c * sW + t * cW) * ((&1 - sW * (uW + a) - cW * a) - cW * vW)` THEN
    C976NTM_PROD `&0 <= c * ((uW + a) - (a - (&18 / &25) * cW))` THEN
    C976NTM_PROD `&0 <= cW * ((c + (&11 / &25) * t) - (u + a))` THEN
    C976NTM_RING `(cW * (c * cW - t * sW) + sW * (c * sW + t * cW)) * (uW + a) = c * (uW + a)` THEN
    C976NTM_PROD `&0 < cW * (c * sW + t * cW)` THEN
    C976NTM_PROD `&0 <= cW * --mn` THEN
    C976NTM_FACT `&0 < c + cW * (c * sW + t * cW) - cW * mn + cW` THEN
    C976NTM_PROD `&0 < cW * (&1 + c * (eta + sW - &43 / &25) - t * (&36 / &25 - cW) - mn)` THEN
    C976NTM_RING `cW * (&1 + c * (eta + sW - &43 / &25) - t * (&36 / &25 - cW) - mn) =
                  (c + cW * (c * sW + t * cW) - cW * mn + cW) -
                  ((&43 / &25) * c * cW + (&11 / &25) * cW * t + (c * sW + t * cW))` THEN
    C976NTM_PROD `&0 < (a - &1) * (c + cW * (c * sW + t * cW) - cW * mn + cW)` THEN
    C976NTM_LIN;
    (* topAxis *)
    UNDISCH_TAC `ABT_upper c (--t) u v a (--sW) cW <= ABT_lower cW sW uW vW a (--sW) cW` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `&0 <= c * cW - t * sW` THENL
     [SUBGOAL_THEN `max (c * cW - t * sW) (&0) = c * cW - t * sW` SUBST_ALL_TAC THENL
       [ASM_REWRITE_TAC[REAL_ARITH `max x (&0) = x <=> &0 <= x`]; ALL_TAC] THEN
      SUBGOAL_THEN
       `forall v0. v0 <= v /\
             &0 < (c * sW + t * cW) * (&1 - c - (&11 / &25) * t) + (c * cW - t * sW) * (&1 + v0) +
                  (&1 - eta - (&18 / &25) * sW)
             ==> false`
       ASSUME_TAC THENL
       [GEN_TAC THEN STRIP_TAC THEN
        C976NTM_PROD `&0 <= (c * sW + t * cW) * ((c + (&11 / &25) * t) - (u + a))` THEN
        C976NTM_PROD `&0 <= (c * cW - t * sW) * (v - v0)` THEN
        C976NTM_FACT `a * ((c * sW + t * cW) + (c * cW - t * sW)) -
                      (c * sW + t * cW) * (c + (&11 / &25) * t) + (c * cW - t * sW) * v0 <= vW` THEN
        C976NTM_PROD `&0 <= cW * (vW - (a * ((c * sW + t * cW) + (c * cW - t * sW)) -
                      (c * sW + t * cW) * (c + (&11 / &25) * t) + (c * cW - t * sW) * v0))` THEN
        C976NTM_PROD `&0 < cW * ((c * sW + t * cW) + (c * cW - t * sW))` THEN
        C976NTM_FACT `&0 < cW * ((c * sW + t * cW) + (c * cW - t * sW)) + cW + sW` THEN
        C976NTM_PROD `&0 < cW * ((c * sW + t * cW) * (&1 - c - (&11 / &25) * t) +
                      (c * cW - t * sW) * (&1 + v0) + (&1 - eta - (&18 / &25) * sW))` THEN
        C976NTM_RING `cW * ((c * sW + t * cW) * (&1 - c - (&11 / &25) * t) +
                      (c * cW - t * sW) * (&1 + v0) + (&1 - eta - (&18 / &25) * sW)) =
                      (cW * ((c * sW + t * cW) + (c * cW - t * sW)) + cW + sW) -
                      (&1 + (&18 / &25) * cW * sW + cW * (c * sW + t * cW) * (c + (&11 / &25) * t) -
                       cW * (c * cW - t * sW) * v0)` THEN
        C976NTM_PROD `&0 < (a - &1) * (cW * ((c * sW + t * cW) + (c * cW - t * sW)) + cW + sW)` THEN
        C976NTM_LIN;
        ALL_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `&37 / &50`)) (concl th))) THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `--(&37 / &50) * c`) THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`c:real`; `t:real`; `cW:real`; `sW:real`] C976NTT_TOP_OUTER_MARGIN) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C976NTM_LIN; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        FIRST_X_ASSUM(MATCH_MP_TAC o SPEC `(&1 / &2) * t - c`) THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(SPECL [`c:real`; `t:real`; `cW:real`; `sW:real`] C976NTT_TOP_MIXED_MARGIN) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C976NTM_LIN; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      SUBGOAL_THEN `max (c * cW - t * sW) (&0) = &0` SUBST_ALL_TAC THENL
       [ASM_REWRITE_TAC[REAL_ARITH `max x (&0) = &0 <=> x <= &0`] THEN C976NTM_LIN; ALL_TAC] THEN
      C976NTM_PROD `&0 <= (c * sW + t * cW) * ((c + (&11 / &25) * t) - (u + a))` THEN
      C976NTM_PROD `&0 <= --(c * cW - t * sW) * --v` THEN
      C976NTM_FACT `a * (c * sW + t * cW) - (c * sW + t * cW) * (c + (&11 / &25) * t) <= vW` THEN
      C976NTM_PROD `&0 <= cW * (vW - (a * (c * sW + t * cW) - (c * sW + t * cW) * (c + (&11 / &25) * t)))` THEN
      C976NTM_PROD `&0 < cW * (c * sW + t * cW)` THEN
      C976NTM_FACT `&0 < cW * (c * sW + t * cW) + cW + sW` THEN
      MP_TAC(SPECL [`c:real`; `t:real`; `cW:real`; `sW:real`] C976NTT_TOP_NEGATIVE_MARGIN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C976NTM_LIN; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      C976NTM_PROD `&0 < cW * ((c * sW + t * cW) * (&1 - c - (&11 / &25) * t) +
                    (&1 - eta - (&18 / &25) * sW))` THEN
      C976NTM_RING `cW * ((c * sW + t * cW) * (&1 - c - (&11 / &25) * t) +
                    (&1 - eta - (&18 / &25) * sW)) =
                    (cW * (c * sW + t * cW) + cW + sW) -
                    (&1 + (&18 / &25) * cW * sW + cW * (c * sW + t * cW) * (c + (&11 / &25) * t))` THEN
      C976NTM_PROD `&0 < (a - &1) * (cW * (c * sW + t * cW) + cW + sW)` THEN
      C976NTM_LIN]]);;
(* Lean: angle *)
let C976NTM_ANGLE = prove
 (`forall c s u v a cW sW uW vW aW t.
     c * c + s * s = &1 /\ &0 < a /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     s = --t /\ &1 < a /\ a = aW /\ &0 < c /\ &0 < t /\ t <= c /\
     &0 <= cW /\ &0 <= sW /\
     linside c s u v a (&7 / &20) (--(&13 / &20)) /\ linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1) (--(&11 / &25)) /\ cc976f_alternative c s u v a /\
     linside cW sW uW vW aW (&0) (&0) /\ ~linside cW sW uW vW aW (--(&18 / &25)) (&0) /\
     sW * (uW + aW) + cW * (vW + aW) <= &1 /\
     ldisj c s u v a cW sW uW vW aW
     ==> &0 < sW /\ cW < (&2 / &3) * sW`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `cW < (&2 / &3) * sW` (fun th -> ASSUME_TAC th THEN REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < cW` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `cW = &0 /\ sW = &0` STRIP_ASSUME_TAC THENL
       [RASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `cW * cW + sW * sW = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
      C976NTM_CONTRARY_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[];
    RASM_ARITH_TAC]);;

(* Lean: angle_of_closed_wall *)
let C976NTM_ANGLE_OF_CLOSED_WALL = prove
 (`forall c s u v a cW sW uW vW aW t.
     c * c + s * s = &1 /\ &0 < a /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     s = --t /\ &1 < a /\ a = aW /\ &0 < c /\ &0 < t /\ t <= c /\
     &0 <= cW /\ &0 <= sW /\
     linside c s u v a (&7 / &20) (--(&13 / &20)) /\ linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1) (--(&11 / &25)) /\ cc976f_alternative c s u v a /\
     linside cW sW uW vW aW (&0) (&0) /\ ~linside cW sW uW vW aW (--(&18 / &25)) (&0) /\
     (forall x y. lclosed cW sW uW vW aW x y ==> y <= &1) /\
     ldisj c s u v a cW sW uW vW aW
     ==> &0 < sW /\ cW < (&2 / &3) * sW`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `uW + aW:real`; `vW + aW:real`] OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MATCH_MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                      `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    C976NTM_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
    can (find_term ((=) `lclosed`)) (concl th))) THEN
  EXISTS_TAC `cW * (uW + aW) - sW * (vW + aW)` THEN ASM_REWRITE_TAC[]);;

(* Lean: nonnegative_top_impossible *)
let C976NTM_NONNEGATIVE_TOP_IMPOSSIBLE = prove
 (`forall c s u v a cW sW uW vW aW t.
     c * c + s * s = &1 /\ &0 < a /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     s = --t /\ &1 < a /\ a = aW /\ &0 < c /\ &0 < t /\ t <= c /\
     &0 < cW /\ &0 <= sW /\ sW <= cW /\
     linside c s u v a (&7 / &20) (--(&13 / &20)) /\ linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1) (--(&11 / &25)) /\ cc976f_alternative c s u v a /\
     linside cW sW uW vW aW (&0) (&0) /\ ~linside cW sW uW vW aW (--(&18 / &25)) (&0) /\
     (forall x y. lclosed cW sW uW vW aW x y ==> y <= &1) /\
     ldisj c s u v a cW sW uW vW aW
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `t:real`]
    C976NTM_ANGLE_OF_CLOSED_WALL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC]; STRIP_TAC] THEN
  RASM_ARITH_TAC);;

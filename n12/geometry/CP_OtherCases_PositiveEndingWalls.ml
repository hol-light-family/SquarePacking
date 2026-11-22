(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/PositiveEndingWalls.lean           *)
(* (N12Compact.Completion.OtherCases.PositiveEndingWalls).  Left-wall        *)
(* alternatives from the one genuine western bar W = (c, s, u, v, a):        *)
(* W.c, W.s, W.loU, W.loV, W.side.  CanonicalScalars.bounds = CCCS_BOUNDS,   *)
(* DerivedWalls.vertical_right / closed_affine_bound = OCDW_*,               *)
(* WallProfile.vertex = OCWPVG_VERTEX, PositiveEndingScalars.*_west_margin = *)
(* OCPES_*_WEST_MARGIN.                                                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_PositiveEndingScalars.ml";;
needs "n12/geometry/CP_OtherCases_DerivedWalls.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

let OCPEW_LIN = NLIN_TAC ~deg2:false [];;
let OCPEW_FACT tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;
let OCPEW_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   OCPEW_LIN; ALL_TAC];;
(* unfold a point fact linside c s u v a x y into its four inequalities *)
let OCPEW_POINT tm = STRIP_ASSUME_TAC (REWRITE_RULE[linside] (ASSUME tm));;

(* Lean: negative *)
let OCPEW_NEGATIVE = prove
 (`forall c s u v a r. c * c + s * s = &1 /\ &0 < a /\
     s = --r /\ &1 < a /\ a <= &1001 / &1000 /\ &0 < c /\ &0 <= r /\ r <= c /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\ linside c s u v a (&0) (&0) /\
     (forall y. &0 <= y ==> y <= &4 / &5 ==> ~linside c s u v a (--(&1)) y)
     ==> --c <= u \/ &1 / &14 < u + a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `--c <= u` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --r`)) THEN
  OCPEW_FACT `c pow 2 + r pow 2 = &1`
    (UNDISCH_TAC `c * c + --r * --r = &1` THEN CONV_TAC REAL_RING) THEN
  MP_TAC(SPECL [`c:real`; `r:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  OCPEW_POINT `linside c (--r) u v a (--(&7 / &20)) (--(&7 / &20))` THEN
  OCPEW_POINT `linside c (--r) u v a (&0) (&0)` THEN
  OCPEW_FACT `--r <= v`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (is_forall o concl)) THEN
    REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (not o is_forall o concl)) THEN
    REAL_ARITH_TAC) THEN
  OCPEW_FACT `&7 * c < &13 * r` OCPEW_LIN THEN
  OCPEW_FACT `&3 / &8 < r` OCPEW_LIN THEN
  OCPEW_FACT `&0 < r` OCPEW_LIN THEN
  OCPEW_FACT `&0 <= &1 + c - &2 * r` OCPEW_LIN THEN
  OCPEW_PROD `&0 <= r * (&1 + c - &2 * r)` THEN
  OCPEW_FACT `&0 <= (&1 + c) * (r / &2 - (&1 - c))`
   (UNDISCH_TAC `&0 <= r * (&1 + c - &2 * r)` THEN UNDISCH_TAC `c pow 2 + r pow 2 = &1` THEN
    REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC) THEN
  OCPEW_FACT `&1 - c <= r / &2`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCPEW_PROD `&0 < (&1 + c) * ((&1 - c) - r / &2)` THEN OCPEW_LIN) THEN
  OCPEW_FACT `forall y. ~linside c (--r) u v a (--(&1)) y`
   (X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    OCPEW_POINT `linside c (--r) u v a (--(&1)) y` THEN
    OCPEW_FACT `&0 < c * y` OCPEW_LIN THEN
    OCPEW_FACT `&0 < y`
     (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      OCPEW_PROD `&0 <= c * --y` THEN OCPEW_LIN) THEN
    OCPEW_FACT `y < &4 / &5`
     (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      OCPEW_PROD `&0 <= r * (y - &4 / &5)` THEN OCPEW_LIN) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (fun th -> is_forall(concl th) &&
      can (term_match [] `forall y. P y ==> Q y ==> ~R y`) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]) THEN
  MP_TAC(SPECL [`c:real`; `--r`; `u:real`; `v:real`; `a:real`; `&0`; `&0`; `--(&1)`]
    OCDW_VERTICAL_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--r`; `u:real`; `v:real`; `a:real`; `u:real`; `v:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
                  DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `--r`; `u:real`; `v:real`; `a:real`; `&1`; `&0`; `--(&1)`;
                `&0`; `&0`; `c * u - --r * v`; `--r * u + c * v`] OCDW_CLOSED_AFFINE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_RID]; DISCH_TAC] THEN
  OCPEW_PROD `&0 < c * (a - &1)` THEN
  OCPEW_PROD `&0 < r * (--(&7 / &20) * (r + c) - v)` THEN
  MP_TAC(SPECL [`c:real`; `r:real`] OCPES_NEGATIVE_WEST_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  OCPEW_FACT `c * (&1 / &14) < c * (u + a)` OCPEW_LIN THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  OCPEW_PROD `&0 <= c * (&1 / &14 - (u + a))` THEN OCPEW_LIN);;

(* Lean: left_line_margin (private) *)
let OCPEW_LEFT_LINE_MARGIN = prove
 (`forall d r. &0 < d /\ &0 <= r /\ r <= d /\ d pow 2 + r pow 2 = &1 /\ &5 * d < &14 * r
         ==> &1001 / &1000 < (&4 / &5) * d + r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `r:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  OCPEW_FACT `d < &87 / &100` OCPEW_LIN THEN
  OCPEW_FACT `&49 / &100 < r`
   (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCPEW_PROD `&0 <= (&87 / &100 - d) * (&87 / &100 + d)` THEN
    OCPEW_PROD `&0 <= (&49 / &100 - r) * (&49 / &100 + r)` THEN
    UNDISCH_TAC `d pow 2 + r pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN OCPEW_LIN) THEN
  OCPEW_LIN);;

(* Lean: positive *)
let OCPEW_POSITIVE = prove
 (`forall c s u v a z. c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ a <= &1001 / &1000 /\ &0 < c /\ &0 <= s /\ s <= c /\
     &0 < z /\ z < &9 / &40 /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\ linside c s u v a (&0) (&0) /\
     ~linside c s u v a (&0) (--z) /\
     (forall y. &0 <= y ==> y <= &4 / &5 ==> ~linside c s u v a (--(&1)) y)
     ==> &7 / &200 < --v /\ (&12 / &113) * (&1 - s) < --v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OCPEW_FACT `c pow 2 + s pow 2 = &1` (ASM_REWRITE_TAC[REAL_POW_2]) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  OCPEW_POINT `linside c s u v a (--(&7 / &20)) (--(&7 / &20))` THEN
  OCPEW_POINT `linside c s u v a (&0) (&0)` THEN
  OCPEW_PROD `&0 <= s * (&7 / &20 - z)` THEN
  OCPEW_FACT `u < --s * z` OCPEW_LIN THEN
  OCPEW_PROD `&0 <= s * z` THEN
  OCPEW_PROD `&0 < c * z` THEN
  OCPEW_FACT `--c * z <= v`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside c s u v a (&0) (--z)` THEN REWRITE_TAC[linside] THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (not o is_forall o concl)) THEN
    REAL_ARITH_TAC) THEN
  OCPEW_PROD `&0 < c * (&9 / &40 - z)` THEN
  OCPEW_FACT `&5 * c < &14 * s` OCPEW_LIN THEN
  OCPEW_FACT `&0 < s` OCPEW_LIN THEN
  OCPEW_FACT `s < &3 / &4`
   (OCPEW_PROD `&0 <= (c - s) * (c + s)` THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCPEW_PROD `&0 <= (s - &3 / &4) * (s + &3 / &4)` THEN
    UNDISCH_TAC `c * c + s * s = &1` THEN OCPEW_LIN) THEN
  OCPEW_FACT `--c <= u`
   (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    OCPEW_PROD `&0 <= (&1 - c) * z` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&0` o check (is_forall o concl)) THEN
    REWRITE_TAC[linside] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (not o is_forall o concl)) THEN
    REAL_ARITH_TAC) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCPEW_LEFT_LINE_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  OCPEW_FACT `forall y. ~linside c s u v a (--(&1)) y`
   (X_GEN_TAC `y:real` THEN DISCH_TAC THEN
    OCPEW_POINT `linside c s u v a (--(&1)) y` THEN
    OCPEW_FACT `&0 < s * y` OCPEW_LIN THEN
    OCPEW_FACT `&0 < y`
     (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      OCPEW_PROD `&0 <= s * --y` THEN OCPEW_LIN) THEN
    OCPEW_FACT `y < &4 / &5`
     (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      OCPEW_PROD `&0 <= c * (y - &4 / &5)` THEN OCPEW_LIN) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real` o check (fun th -> is_forall(concl th) &&
      can (term_match [] `forall y. P y ==> Q y ==> ~R y`) (concl th))) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE]) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&0`; `&0`; `--(&1)`]
    OCDW_VERTICAL_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u:real`; `v + a`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
                  DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&1`; `&0`; `--(&1)`;
                `&0`; `&0`; `c * u - s * (v + a)`; `s * u + c * (v + a)`] OCDW_CLOSED_AFFINE_BOUND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_RID]; DISCH_TAC] THEN
  OCPEW_FACT `(&7 / &20) * (c - s) < --v` OCPEW_LIN THEN
  OCPEW_FACT `s * ((&13 / &20) / s) = &13 / &20`
   (MATCH_MP_TAC REAL_DIV_LMUL THEN OCPEW_LIN) THEN
  OCPEW_FACT `s * ((&7 / &20) * (c - s) + &1 - (&13 / &20) / s) =
              (&7 / &20) * s * (c - s) + s - &13 / &20`
   (POP_ASSUM MP_TAC THEN REAL_ARITH_TAC) THEN
  OCPEW_PROD `&0 < c * (--(&7 / &20) * (c + s) - u)` THEN
  OCPEW_PROD `&0 < s * (a - &1)` THEN
  OCPEW_FACT `s * ((&7 / &20) * (c - s) + &1 - (&13 / &20) / s) < s * --v`
   (ASM_REWRITE_TAC[] THEN
    MAP_EVERY (MP_TAC o ASSUME)
     [`c * c + s * s = &1`; `&0 < c * (--(&7 / &20) * (c + s) - u)`; `&0 < s * (a - &1)`;
      `--(&1) <= &1 * (c * u - s * (v + a)) + &0 * (s * u + c * (v + a))`] THEN
    REAL_ARITH_TAC) THEN
  OCPEW_FACT `(&7 / &20) * (c - s) + &1 - (&13 / &20) / s < --v`
   (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OCPEW_PROD `&0 <= s * ((&7 / &20) * (c - s) + &1 - (&13 / &20) / s - --v)` THEN
    POP_ASSUM MP_TAC THEN
    UNDISCH_TAC `s * ((&7 / &20) * (c - s) + &1 - (&13 / &20) / s) < s * --v` THEN
    REAL_ARITH_TAC) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] OCPES_POSITIVE_WEST_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(&7 / &20) * (c - s) < --v` THEN
  UNDISCH_TAC `(&7 / &20) * (c - s) + &1 - (&13 / &20) / s < --v` THEN
  REAL_ARITH_TAC);;

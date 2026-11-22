(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeCentralOrder.lean      *)
(* (N12Compact.Completion.OtherCases.C983.NegativeCentralOrder).  Exact      *)
(* scalar comparisons for the two actual central negative frames.  The two   *)
(* bottom alternatives are retained.  Squares E, N are cE sE uE vE aE,       *)
(* cN sN uN vN aN (unit normals / positive sides explicit).                  *)
(* NegativeTripleFaces.Data E t = ccntf_data; TopOnlyQuadrantProfile.Data =  *)
(* octoqp_data; TopOnlyQuadrantScalars.profile_bounds = OCTOQS_PROFILE_BOUNDS;*)
(* upper / lower / strict_bounds / ownV = ABT_*; CanonicalScalars.bounds =   *)
(* CCCS_BOUNDS; C981CompletionSupportForms.lower_negative_pos /             *)
(* upper_in_bands = C981SF_*; WallProfile.upper_neg / lower_neg = OCWPVG_*;  *)
(* faceSeparation_of_disjoint + separated + radii = ABT_FOUR_AXES.          *)
(* Tag C983NCO_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeRightSeparation.ml";;

let C983NCO_LIN = NLIN_TAC ~deg2:false [];;

let C983NCO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC THEN
   C983NCO_LIN; ALL_TAC];;

(* x * y < x * z with 0 < x gives y < z *)
let C983NCO_CANCEL_TAC x =
  MATCH_MP_TAC(SPEC x (MESON[REAL_LT_LMUL_EQ] `forall x y z. &0 < x /\ (&0 < x ==> x * y < x * z) ==> y < z`)) THEN
  CONJ_TAC THENL [C983NCO_LIN; DISCH_TAC];;

let C983NCO_E_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[ccntf_data; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`));;

(* Lean: first_bar_sine_lt *)
let C983NCO_FIRST_BAR_SINE_LT = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t /\
     (&4 / &5) * t - c <= v
     ==> t < &29 / &100`,
  C983NCO_E_TAC THEN
  SUBGOAL_THEN `&40 + &11 * t < &45 * c` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 < (&45 * c - (&40 + &11 * t)) * (&45 * c + (&40 + &11 * t))` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C983NCO_PROD `&0 <= (t - &29 / &100) * (t + &29 / &100)` THEN
  C983NCO_LIN);;

(* Lean: north_sine_gt *)
let C983NCO_NORTH_SINE_GT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ octoqp_data c s u v a
     ==> &29 / &100 < --s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[octoqp_data] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&50 * (&1 + s) < &37 * c` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C983NCO_PROD `&0 < (&37 * c - &50 * (&1 + s)) * (&37 * c + &50 * (&1 + s))` THEN
  C983NCO_PROD `&0 < (&1 + s) * (&1131 + &3869 * s)` THEN
  C983NCO_LIN);;

(* Lean: upperV_gt_sum *)
let C983NCO_UPPERV_GT_SUM = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t /\ &1 / &5 <= t
     ==> c + t - &1 < v + a`,
  C983NCO_E_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C983NCO_PROD `&0 <= t * (t - &1 / &5)` THEN
    C983NCO_PROD `&0 <= (&1 - c) * (&1 - c)` THEN C983NCO_LIN;
    C983NCO_PROD `&0 < c * (a - &1)` THEN
    C983NCO_PROD `&0 < t * ((u + a) - &1)` THEN
    C983NCO_PROD `&0 <= (&1 - c) * (c + t - &1)` THEN
    C983NCO_CANCEL_TAC `c:real` THEN C983NCO_LIN]);;

(* Lean: ordered_normals *)
let C983NCO_ORDERED_NORMALS = prove
 (`forall c t d r.
     &0 < c /\ &0 < t /\ &0 < d /\ &0 < r /\ t <= c /\
     c pow 2 + t pow 2 = &1 /\ d pow 2 + r pow 2 = &1 /\ r <= t
     ==> c <= d /\ d + r <= c + t /\ &0 <= d * t - c * r /\ c <= r * t + d * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  C983NCO_PROD `&0 <= (t - r) * (t + r)` THEN
  SUBGOAL_THEN `c <= d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NCO_PROD `&0 < (c - d) * (c + d)` THEN C983NCO_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `r <= d` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 <= (t - r) * (c + d - t - r)` THEN
  SUBGOAL_THEN `(c + t - d - r) * (c + d) = (t - r) * (c + d - t - r)` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + t * t = &1` THEN UNDISCH_TAC `d * d + r * r = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `d + r <= c + t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NCO_PROD `&0 < (d + r - c - t) * (c + d)` THEN C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 <= d * (t - r)` THEN
  C983NCO_PROD `&0 <= r * (d - c)` THEN
  SUBGOAL_THEN `&0 <= d * t - c * r` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `d <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NCO_PROD `&0 < (d - &1) * (d + &1)` THEN
    C983NCO_PROD `&0 <= r * r` THEN C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 < r * t` THEN C983NCO_PROD `&0 < d * c` THEN
  C983NCO_PROD `&0 <= r * (d * t - c * r)` THEN
  C983NCO_PROD `&0 <= (r * t + d * c) * (&1 - d)` THEN
  SUBGOAL_THEN `(r * t + d * c) * d - c = r * (d * t - c * r)` ASSUME_TAC THENL
   [UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN C983NCO_LIN);;

(* scalar core of north_lower_cap: A = t*d - c*r, B = t*r + c*d,            *)
(* P = d + r - 11/25*d*r, Q = d - r + 11/25*r^2 (Lean local lets)            *)
let C983NCO_NORTH_LOWER_CAP_CORE = prove
 (`forall c t d r u v a.
     &0 < c /\ &0 < t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\
     &0 < d /\ &0 < r /\ d pow 2 + r pow 2 = &1 /\ r <= t /\ &1 < a /\
     --r <= u /\ u + a <= d - (&14 / &25) * r /\ v + a <= d + r
     ==> (t * d - c * r) * u + (t * r + c * d) * v <= c + t - &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `d:real`; `r:real`] C983NCO_ORDERED_NORMALS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `r <= d` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t * d - c * r` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 < t * r` THEN C983NCO_PROD `&0 < c * d` THEN
  SUBGOAL_THEN `d <= &1 /\ r <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [C983NCO_PROD `&0 < (d - &1) * (d + &1)` THEN C983NCO_PROD `&0 <= r * r`;
      C983NCO_PROD `&0 < (r - &1) * (r + &1)` THEN C983NCO_PROD `&0 <= d * d`] THEN
    C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 <= r * r` THEN
  SUBGOAL_THEN `&0 <= d - r + &11 / &25 * r * r` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 <= r * (&2 - &11 / &25 * (d + r))` THEN
  SUBGOAL_THEN `&0 <= (d + r - &11 / &25 * d * r) - (d - r + &11 / &25 * r * r)`
    ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= d + r - &11 / &25 * d * r` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `r * (d + r - &11 / &25 * d * r) + d * (d - r + &11 / &25 * r * r) = &1`
    ASSUME_TAC THENL
   [UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C983NCO_PROD `&0 <= (d + r - &11 / &25 * d * r) * (c + d - t - r)` THEN
  C983NCO_PROD `&0 <= ((d + r - &11 / &25 * d * r) - (d - r + &11 / &25 * r * r)) * (t + r)` THEN
  SUBGOAL_THEN `&0 <= (d + r - &11 / &25 * d * r) * (c + d) - (d - r + &11 / &25 * r * r) * (t + r)`
    ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 <= (t - r) * ((d + r - &11 / &25 * d * r) * (c + d) -
                                 (d - r + &11 / &25 * r * r) * (t + r))` THEN
  SUBGOAL_THEN `(c + d) * (t * (d + r - &11 / &25 * d * r) + c * (d - r + &11 / &25 * r * r) - &1) =
                (t - r) * ((d + r - &11 / &25 * d * r) * (c + d) -
                           (d - r + &11 / &25 * r * r) * (t + r))` ASSUME_TAC THENL
   [UNDISCH_TAC `d * d + r * r = &1` THEN UNDISCH_TAC `c * c + t * t = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= t * (d + r - &11 / &25 * d * r) + c * (d - r + &11 / &25 * r * r)`
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NCO_PROD `&0 < (&1 - (t * (d + r - &11 / &25 * d * r) + c * (d - r + &11 / &25 * r * r))) * (c + d)` THEN
    C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 <= (t * d - c * r) * ((d - &14 / &25 * r - &1) - u)` THEN
  C983NCO_PROD `&0 <= (t * r + c * d) * ((d + r - &1) - v)` THEN
  SUBGOAL_THEN `(t * d - c * r) * (d - &14 / &25 * r - &1) + (t * r + c * d) * (d + r - &1) =
                c + t - (t * (d + r - &11 / &25 * d * r) + c * (d - r + &11 / &25 * r * r))`
    ASSUME_TAC THENL
   [UNDISCH_TAC `d * d + r * r = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C983NCO_LIN);;

(* Lean: north_lower_cap *)
let C983NCO_NORTH_LOWER_CAP = prove
 (`forall cE sE uE vE aE cN sN uN vN aN t.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     ccntf_data cE sE uE vE aE t /\ octoqp_data cN sN uN vN aN /\
     &1 < aN /\ --sN <= t
     ==> ABT_lower cN sN uN vN aN t cE <= cE + t - &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ccntf_data; octoqp_data; IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sE = --t`)) THEN
  MP_TAC(SPECL [`cE:real`; `t:real`; `cN:real`; `--sN`; `uN:real`; `vN:real`; `aN:real`]
    C983NCO_NORTH_LOWER_CAP_CORE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_POW_2; REAL_NEG_NEG] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `--sN`;
                `t:real`; `cE:real`] C981SF_LOWER_NEGATIVE_POS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[REAL_NEG_NEG] THEN
    MP_TAC(SPECL [`cE:real`; `t:real`; `cN:real`; `--sN`] C983NCO_ORDERED_NORMALS) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
                    STRIP_TAC] THEN
    CONJ_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
    C983NCO_PROD `&0 < t * --sN` THEN C983NCO_PROD `&0 < cE * cN` THEN C983NCO_LIN;
    DISCH_THEN SUBST1_TAC] THEN
  REAL_ARITH_TAC);;

(* Lean: southeast_upper_floor *)
let C983NCO_SOUTHEAST_UPPER_FLOOR = prove
 (`forall cE sE uE vE aE cN sN uN vN aN t.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     ccntf_data cE sE uE vE aE t /\ octoqp_data cN sN uN vN aN /\
     --(&1) <= --t * (uE + aE) + cE * vE /\ --sN <= t
     ==> cN - sN - &1 < ABT_upper cE sE uE vE aE (--sN) cN`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ccntf_data; octoqp_data; IMP_CONJ] THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sE = --t`)) THEN
  MP_TAC(SPECL [`cE:real`; `t:real`; `cN:real`; `--sN`] C983NCO_ORDERED_NORMALS) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
                  STRIP_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `--sN * cE - cN * t <= &0` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 < --sN * t` THEN C983NCO_PROD `&0 < cN * cE` THEN
  SUBGOAL_THEN `&0 < --sN * t + cN * cE` ASSUME_TAC THENL [C983NCO_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_upper cE (--t) uE vE aE (--sN) cN =
                (--sN * cE - cN * t) * uE + (--sN * t + cN * cE) * (vE + aE)`
    SUBST1_TAC THENL
   [REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(--sN * cE + cN * --t) = --(--sN * cE - cN * t) /\
                  abs(-- --sN * --t + cN * cE) = --sN * t + cN * cE`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `cE * ((--sN * cE - cN * t) * uE + (--sN * t + cN * cE) * (vE + aE)) =
                --sN * uE + (--sN * t + cN * cE) * (cE * (vE + aE) - t * uE)` ASSUME_TAC THENL
   [UNDISCH_TAC `cE * cE + --t * --t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(cE + t) * aE - &1 <= cE * (vE + aE) - t * uE` ASSUME_TAC THENL
   [C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 <= (--sN * t + cN * cE) * ((cE * (vE + aE) - t * uE) - ((cE + t) * aE - &1))` THEN
  SUBGOAL_THEN `&0 < (--sN * t + cN * cE) * ((cE + t) * (aE - &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 <= --sN * uE` THEN
  C983NCO_PROD `&0 <= ((--sN * t + cN * cE) - cE) * (cE + t - &1)` THEN
  C983NCO_PROD `&0 <= cE * ((cE + t) - (cN + --sN))` THEN
  C983NCO_CANCEL_TAC `cE:real` THEN C983NCO_LIN);;

(* Lean: central_cone (private) *)
let C983NCO_CENTRAL_CONE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN nx ny.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&0) (&31 / &50) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cN sN uN vN aN nx ny
     ==> &0 < ny /\ &0 < (&53 / &200) * nx + (&1 / &8) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `&13 / &50`; `&0`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `&21 / &40`; `&1 / &8`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `&0`; `&31 / &50`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN RASM_ARITH_TAC);;

(* Lean: central_separators *)
let C983NCO_CENTRAL_SEPARATORS = prove
 (`forall cE sE uE vE aE cN sN uN vN aN t.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     aE = aN /\ ccntf_data cE sE uE vE aE t /\ octoqp_data cN sN uN vN aN /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&0) (&31 / &50) /\
     ldisj cE sE uE vE aE cN sN uN vN aN
     ==> ABT_upper cE sE uE vE aE (--sE) cE <= ABT_lower cN sN uN vN aN (--sE) cE \/
         ABT_upper cE sE uE vE aE (--sN) cN <= ABT_lower cN sN uN vN aN (--sN) cN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 < aN` ASSUME_TAC THENL
   [UNDISCH_TAC `ccntf_data cE sE uE vE aE t` THEN REWRITE_TAC[ccntf_data] THEN
    STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] OCTOQS_PROFILE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o filter (not o is_eq o concl) o CONJUNCTS o
    REWRITE_RULE[ccntf_data] o check (fun th -> concl th = `ccntf_data cE sE uE vE aE t`)) THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[octoqp_data] o
    check (fun th -> concl th = `octoqp_data cN sN uN vN aN`)) THEN
  SUBGOAL_THEN `sE < &0 /\ --sE <= &2 * cE` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ccntf_data cE sE uE vE aE t` THEN REWRITE_TAC[ccntf_data] THEN
    STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  let tE = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
  and tN = [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] in
  let cone nx ny =
    MP_TAC(SPECL (tE @ tN @ [nx; ny]) C983NCO_CENTRAL_CONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
      STRIP_TAC THEN RASM_ARITH_TAC] in
  MP_TAC(SPECL (tE @ tN) ABT_FOUR_AXES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C983NRS_REVERSE th))) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         cone `cE:real` `sE:real`; cone `--cE` `--sE`; cone `sE:real` `--cE`;
         cone `cN:real` `sN:real`; cone `--cN` `--sN`; cone `sN:real` `--cN`]);;

(* Lean: sine_lt *)
let C983NCO_SINE_LT = prove
 (`forall cE sE uE vE aE cN sN uN vN aN t.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     aE = aN /\ ccntf_data cE sE uE vE aE t /\ octoqp_data cN sN uN vN aN /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cN sN uN vN aN (&21 / &40) (&1 / &8) /\
     linside cN sN uN vN aN (&0) (&31 / &50) /\
     ldisj cE sE uE vE aE cN sN uN vN aN
     ==> t < --sN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < aN` ASSUME_TAC THENL
   [UNDISCH_TAC `ccntf_data cE sE uE vE aE t` THEN REWRITE_TAC[ccntf_data] THEN
    STRIP_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] C983NCO_NORTH_SINE_GT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&4 / &5) * t - cE <= vE \/ --(&1) <= --t * (uE + aE) + cE * vE`
    MP_TAC THENL
   [UNDISCH_TAC `ccntf_data cE sE uE vE aE t` THEN SIMP_TAC[ccntf_data]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `t:real`]
      C983NCO_FIRST_BAR_SINE_LT) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sE = --t` ASSUME_TAC THENL
   [UNDISCH_TAC `ccntf_data cE sE uE vE aE t` THEN SIMP_TAC[ccntf_data]; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `t:real`]
    C983NCO_CENTRAL_SEPARATORS) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sE = --t`)) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(SPECL [`cE:real`; `--t`; `uE:real`; `vE:real`; `aE:real`;
                  `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `t:real`]
      C983NCO_NORTH_LOWER_CAP) THEN
    MP_TAC(SPECL [`cE:real`; `--t`; `uE:real`; `vE:real`; `aE:real`; `t:real`]
      C983NCO_UPPERV_GT_SUM) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN RASM_ARITH_TAC;
    MP_TAC(SPECL [`cE:real`; `--t`; `uE:real`; `vE:real`; `aE:real`;
                  `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `t:real`]
      C983NCO_SOUTHEAST_UPPER_FLOOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `octoqp_data cN sN uN vN aN` THEN REWRITE_TAC[octoqp_data] THEN
    REPEAT STRIP_TAC THEN RASM_ARITH_TAC]);;

(* Lean: cosine_gt_six_sevenths *)
let C983NCO_COSINE_GT_SIX_SEVENTHS = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t
     ==> &6 / &7 < c`,
  C983NCO_E_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C983NCO_LIN; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C983NCO_PROD `&0 <= (&6 / &7 - c) * (&6 / &7 + c)` THEN
  SUBGOAL_THEN `&1 / &2 < t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983NCO_PROD `&0 <= (&1 / &2 - t) * (&1 / &2 + t)` THEN C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 < (c - &1 / &2) * (t - &1 / &2)` THEN
  SUBGOAL_THEN `&4 / &3 < c + t` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C983NCO_PROD `&0 <= (c + t - &1) * (&4 / &3 - (c + t))` THEN C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 < ((c + t) - &4 / &3) * (&1 - (&21 / &80) * ((c + t) + &4 / &3))` THEN
  SUBGOAL_THEN `&0 < c + t - &1 - (&21 / &40) * c * t - (&1 / &8) * c * c` ASSUME_TAC THENL
   [C983NCO_LIN; ALL_TAC] THEN
  C983NCO_PROD `&0 < c * (a - &1)` THEN
  C983NCO_PROD `&0 < t * ((u + a) - &1)` THEN
  C983NCO_PROD `&0 <= c * (((&21 / &40) * t + (&1 / &8) * c) - (v + a))` THEN
  C983NCO_LIN);;

(* Lean: upper_vertex_y_gt *)
let C983NCO_UPPER_VERTEX_Y_GT =
  let common =
    FIRST_X_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[ccntf_data] o
      check (fun th -> concl th = `ccntf_data c s u v a t`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
    MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
    ANTS_TAC THENL [REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC; STRIP_TAC] in
  prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t
     ==> --(&1) / &7 < --t * (u + a) + c * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&4 / &5) * t - c <= v \/ --(&1) <= --t * (u + a) + c * v` MP_TAC THENL
   [UNDISCH_TAC `ccntf_data c s u v a t` THEN SIMP_TAC[ccntf_data]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`]
      C983NCO_FIRST_BAR_SINE_LT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    common THEN
    C983NCO_PROD `&0 < (&29 / &100 - t) * (&29 / &100 + t)` THEN
    SUBGOAL_THEN `&19 / &20 < c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C983NCO_PROD `&0 <= (&19 / &20 - c) * (&19 / &20 + c)` THEN C983NCO_LIN; ALL_TAC] THEN
    C983NCO_PROD `&0 < t * ((&13 / &50) * c - u)` THEN
    C983NCO_PROD `&0 <= c * (v - ((&4 / &5) * t - c))` THEN
    C983NCO_PROD `&0 < (c - t) * (a - &1)` THEN
    C983NCO_PROD `&0 <= c * (&1 - c)` THEN
    C983NCO_PROD `&0 < t * (c - &19 / &20)` THEN
    C983NCO_LIN;
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`]
      C983NCO_COSINE_GT_SIX_SEVENTHS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    common THEN
    C983NCO_PROD `&0 < c * (a - &1)` THEN
    C983NCO_LIN]);;

(* Lean: north_projection_lt *)
let C983NCO_NORTH_PROJECTION_LT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ octoqp_data c s u v a
     ==> c + --s / &7 < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C983NCO_NORTH_SINE_GT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `octoqp_data c s u v a` THEN REWRITE_TAC[octoqp_data] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--s <= &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NCO_PROD `&0 < (--s - &1) * (--s + &1)` THEN
    C983NCO_PROD `&0 <= c * c` THEN C983NCO_LIN; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C983NCO_PROD `&0 <= (c - (&1 - --s / &7)) * (c + (&1 - --s / &7))` THEN
  C983NCO_PROD `&0 < --s * (&50 * --s - &14)` THEN
  C983NCO_LIN);;

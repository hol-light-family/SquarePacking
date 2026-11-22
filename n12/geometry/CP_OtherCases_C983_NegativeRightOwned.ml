(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeRightOwned.lean        *)
(* (N12Compact.Completion.OtherCases.C983.NegativeRightOwned).  Exact        *)
(* support bounds for the branch in which both separating normals belong to  *)
(* the right square; the genuine northeast profile and both southeast bottom *)
(* alternatives are retained.  Squares E, N, R are cE sE uE vE aE,           *)
(* cN sN uN vN aN, cR sR uR vR aR (unit normals / positive sides explicit).  *)
(* RightTripleData.Input / RightProfile = ocrtd_input / ocrtd_rightprofile;  *)
(* NegativeTripleFaces.Data = ccntf_data; TopOnlyQuadrantProfile.Data =      *)
(* octoqp_data; upper / lower / ownU / ownV = ABT_upper / ABT_lower /        *)
(* ABT_OWNU / ABT_OWNV; C981CompletionSupportForms.upper_in_bands =          *)
(* C981SF_UPPER_IN_BANDS; CommonCases.CanonicalScalars.bounds = CCCS_BOUNDS; *)
(* NegativeCentralOrder.north_sine_gt = C983NCO_NORTH_SINE_GT;               *)
(* NegativeWallElimination.* = OC983NWE_*;                                   *)
(* NegativeTripleNorthSeparation.right_axis_bounds = OCNTNS_RIGHT_AXIS_BOUNDS;*)
(* TopOnlyQuadrantScalars.profile_bounds = OCTOQS_PROFILE_BOUNDS.            *)
(* Lean `let` abbreviations are written out.  Tag C983NRO_.                  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeCentralOrder.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeWallElimination.ml";;
needs "n12/geometry/CP_OtherCases_NegativeTripleNorthSeparation.ml";;
needs "n12/geometry/CP_OtherCases_RightTripleData.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyQuadrantScalars.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/ABTransverse.ml";;

let C983NRO_LIN = NLIN_TAC ~deg2:false [];;

let C983NRO_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [(MATCH_MP_TAC REAL_LT_MUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN CONJ_TAC THEN
   FIRST [MATCH_ACCEPT_TAC REAL_LE_POW_2; C983NRO_LIN]; ALL_TAC];;

let C983NRO_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C983NRO_LIN; ALL_TAC];;

let C983NRO_RING tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
     type_of(lhs(concl th)) = `:real`))) THEN CONV_TAC REAL_RING; ALL_TAC];;

let C983NRO_POS_CANCEL = prove
 (`forall c g. &0 < c /\ &0 < c * g ==> &0 < g`,
  MESON_TAC[REAL_LT_MUL_EQ]);;

let C983NRO_NN_CANCEL = prove
 (`forall c g. &0 < c /\ &0 <= c * g ==> &0 <= g`,
  MESON_TAC[REAL_LE_MUL_EQ]);;

let C983NRO_UNIT_LE = prove
 (`forall x y. x pow 2 + y pow 2 = &1 ==> x <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `x - &1`; SQ_NONNEG `y:real`]);;

(* Lean: unit_sum (private) *)
let C983NRO_UNIT_SUM = prove
 (`forall a b. &0 < a /\ &0 <= b /\ a pow 2 + b pow 2 = &1 ==> &1 + (&4 / &5) * a * b <= a + b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `b <= a \/ a <= b`) THENL
   [MP_TAC(SPECL [`a:real`; `b:real`] CCCS_BOUNDS) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    MP_TAC(SPECL [`b:real`; `a:real`] CCCS_BOUNDS) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY C983NRO_LIN THEN
      UNDISCH_TAC `a pow 2 + b pow 2 = &1` THEN REAL_ARITH_TAC;
      STRIP_TAC THEN C983NRO_LIN]]);;

(* Lean: upper_pp (private) *)
let C983NRO_UPPER_PP = prove
 (`forall c s u v a nx ny.
     &0 <= nx * c + ny * s /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* Lean: upper_pn (private) *)
let C983NRO_UPPER_PN = prove
 (`forall c s u v a nx ny.
     &0 <= nx * c + ny * s /\ --nx * s + ny * c <= &0
     ==> ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REAL_ARITH_TAC);;

(* Lean: north_floor *)
let C983NRO_NORTH_FLOOR = prove
 (`forall c s u v a h k.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ octoqp_data c s u v a /\
     &0 < h /\ &0 <= k /\ k < &3 / &4 /\ h pow 2 + k pow 2 = &1
     ==> &1 - k < ABT_upper c s u v a h (--k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[octoqp_data] THEN STRIP_TAC THEN
  C983NRO_PROD `&0 < h * c` THEN C983NRO_PROD `&0 <= k * --s` THEN
  MP_TAC(SPECL [`h:real`; `k:real`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`--s`; `c:real`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; DISCH_TAC] THEN
  C983NRO_RING `(h * c + k * --s) pow 2 + (h * --s - k * c) pow 2 = &1` THEN
  C983NRO_RING `c pow 2 + (--s) pow 2 = &1` THEN
  ASM_CASES_TAC `&0 <= h * --s - k * c` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `--k`]
      C983NRO_UPPER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C983NRO_LIN; DISCH_THEN SUBST1_TAC] THEN
    C983NRO_PROD `&0 <= --s * (&1 - h)` THEN C983NRO_PROD `&0 <= k * c` THEN
    C983NRO_FACT `h * --s - k * c <= --s` THEN
    C983NRO_PROD `&0 <= (--s - (h * --s - k * c)) * (--s + (h * --s - k * c))` THEN
    SUBGOAL_THEN `c <= h * c + k * --s` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NRO_PROD `&0 < (c - (h * c + k * --s)) * (c + (h * c + k * --s))` THEN
      C983NRO_LIN; ALL_TAC] THEN
    MP_TAC(SPECL [`h * c + k * --s`; `h * --s - k * c`] C983NRO_UNIT_SUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    C983NRO_PROD `&0 <= (h * --s - k * c) * ((&4 / &5) * (h * c + k * --s) - (&37 / &50) * c)` THEN
    C983NRO_PROD `&0 < (h * c + k * --s) * ((u + a) - (&1 - --s))` THEN
    C983NRO_PROD `&0 <= (h * --s - k * c) * ((v + a) - (&1 + (&13 / &50) * c))` THEN
    C983NRO_RING `k * c pow 2 + k * (--s) pow 2 = k` THEN
    C983NRO_LIN;
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `--k`]
      C983NRO_UPPER_PN) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C983NRO_LIN; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(SPECL [`h * c + k * --s`; `--(h * --s - k * c)`] C983NRO_UNIT_SUM) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY C983NRO_LIN THEN
      UNDISCH_TAC `(h * c + k * --s) pow 2 + (h * --s - k * c) pow 2 = &1` THEN
      CONV_TAC REAL_RING; DISCH_TAC] THEN
    C983NRO_RING `k * (h * c + k * --s) - --s = h * --(h * --s - k * c)` THEN
    C983NRO_PROD `&0 <= h * --(h * --s - k * c)` THEN
    C983NRO_PROD `&0 < (h * c + k * --s) * (&3 / &4 - k)` THEN
    C983NRO_PROD `&0 <= --(h * --s - k * c) * ((&4 / &5) * (h * c + k * --s) - --s)` THEN
    C983NRO_PROD `&0 < (h * c + k * --s) * ((u + a) - (&1 - --s))` THEN
    C983NRO_PROD `&0 <= --(h * --s - k * c) * ((c + --s - &1) - v)` THEN
    C983NRO_RING `k * c pow 2 + k * (--s) pow 2 = k` THEN
    C983NRO_LIN]);;
let C983NRO_UPPER_IN_BANDS_NP = prove
 (`forall c s u v a nx ny.
     nx * c + ny * s <= &0 /\ &0 <= --nx * s + ny * c
     ==> ABT_upper c s u v a nx ny =
         (nx * c + ny * s) * u + (--nx * s + ny * c) * (v + a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REAL_ARITH_TAC);;

let C983NRO_E_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[ccntf_data; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`));;
(* Lean: north_shallow_floor *)
let C983NRO_NORTH_SHALLOW_FLOOR = prove
 (`forall c s u v a h k.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ octoqp_data c s u v a /\
     &0 < h /\ &0 <= k /\ k <= &9 / &41 /\ h pow 2 + k pow 2 = &1
     ==> (&26 / &25) * h - k < ABT_upper c s u v a h (--k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCTOQS_PROFILE_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C983NCO_NORTH_SINE_GT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `octoqp_data c s u v a` THEN REWRITE_TAC[octoqp_data] THEN STRIP_TAC THEN
  C983NRO_RING `c pow 2 + (--s) pow 2 = &1` THEN
  C983NRO_PROD `&0 <= ((c + --s) - &31 / &25) * (&10 / &7 - (c + --s))` THEN
  C983NRO_FACT `&26 / &25 < c + --s - (&37 / &50) * c * --s` THEN
  C983NRO_FACT `&1 < (&37 / &50) * c + --s` THEN
  MP_TAC(SPECL [`c:real`; `--s`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C983NRO_PROD `&0 <= (&1 - c) * (&1 - (&37 / &50) * c)` THEN
  C983NRO_FACT `c - --s + &13 / &50 + (&37 / &50) * (--s) pow 2 < &1` THEN
  C983NRO_PROD `&0 <= (&9 / &41 - k) * (&9 / &41 + k)` THEN
  SUBGOAL_THEN `&40 / &41 <= h` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NRO_PROD `&0 < (&40 / &41 - h) * (&40 / &41 + h)` THEN C983NRO_LIN; ALL_TAC] THEN
  C983NRO_PROD `&0 < h * c` THEN C983NRO_PROD `&0 <= k * --s` THEN
  C983NRO_PROD `&0 < (--s - &29 / &100) * h` THEN
  C983NRO_PROD `&0 <= k * (&1 - c)` THEN
  C983NRO_FACT `&0 < h * --s - k * c` THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `h:real`; `--k`]
    C983NRO_UPPER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C983NRO_LIN; DISCH_THEN SUBST1_TAC] THEN
  C983NRO_PROD `&0 < (h * c + k * --s) * ((u + a) - (&1 - --s))` THEN
  C983NRO_PROD `&0 <= (h * --s - k * c) * ((v + a) - (&1 + (&13 / &50) * c))` THEN
  C983NRO_PROD `&0 < h * ((c + --s - (&37 / &50) * c * --s) - &26 / &25)` THEN
  C983NRO_PROD `&0 <= k * (&1 - (c - --s + &13 / &50 + (&37 / &50) * (--s) pow 2))` THEN
  C983NRO_RING `k * c pow 2 + k * (--s) pow 2 = k` THEN
  C983NRO_LIN);;

(* Lean: southeast_first_minorant (private) *)
let C983NRO_SOUTHEAST_FIRST_MINORANT = prove
 (`forall c s u v a t h k.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t /\
     (&4 / &5) * t - c <= v /\ &0 < h /\ &0 <= k
     ==> (&0 <= k * c - h * t
          ==> (k * c - h * t) + (k * t + h * c) * (&1 + (&4 / &5) * t - c) <
              ABT_upper c s u v a k h) /\
         (k * c - h * t <= &0
          ==> (&13 / &50) * c * (k * c - h * t) +
              (k * t + h * c) * (&1 + (&4 / &5) * t - c) < ABT_upper c s u v a k h)`,
  C983NRO_E_TAC THEN
  C983NRO_PROD `&0 <= k * t` THEN C983NRO_PROD `&0 < h * c` THEN
  C983NRO_PROD `&0 < (k * t + h * c) * ((v + a) - (&1 + (&4 / &5) * t - c))` THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `k:real`; `h:real`]
      C983NRO_UPPER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C983NRO_LIN; DISCH_THEN SUBST1_TAC] THEN
    C983NRO_PROD `&0 <= (k * c - h * t) * ((u + a) - &1)` THEN C983NRO_LIN;
    MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `k:real`; `h:real`]
      C983NRO_UPPER_IN_BANDS_NP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C983NRO_LIN; DISCH_THEN SUBST1_TAC] THEN
    C983NRO_PROD `&0 <= --(k * c - h * t) * ((&13 / &50) * c - u)` THEN C983NRO_LIN]);;
(* Lean: first_steeper (private) *)
let C983NRO_FIRST_STEEPER = prove
 (`forall c t h k.
     &0 < c /\ &0 < t /\ &0 < h /\ &0 <= k /\
     c pow 2 + t pow 2 = &1 /\ h pow 2 + k pow 2 = &1 /\ k * c - h * t <= &0
     ==> &1 + (&4 / &5) * k - h <=
         (&13 / &50) * c * (k * c - h * t) + (k * t + h * c) * (&1 + (&4 / &5) * t - c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983NRO_PROD `&0 < h * c` THEN C983NRO_PROD `&0 <= k * t` THEN
  C983NRO_RING `(h * c + k * t) pow 2 + (h * t - k * c) pow 2 = &1` THEN
  MP_TAC(SPECL [`h * c + k * t`; `h * t - k * c`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`h:real`; `k:real`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C983NRO_PROD `&0 <= t * (&1 - h)` THEN C983NRO_PROD `&0 <= k * c` THEN
  C983NRO_FACT `h * t - k * c <= t` THEN
  C983NRO_RING `(&13 / &50) * c * (k * c - h * t) + (k * t + h * c) * (&1 + (&4 / &5) * t - c) -
                (&1 + (&4 / &5) * k - h) =
                (h * t - k * c) * ((&27 / &50) * c + t) - (&1 - (h * c + k * t))` THEN
  C983NRO_PROD `&0 <= (h * t - k * c) * (t - (h * t - k * c))` THEN
  C983NRO_PROD `&0 <= (h * c + k * t) * (&1 - (h * c + k * t))` THEN
  C983NRO_PROD `&0 <= (h * t - k * c) * c` THEN
  C983NRO_LIN);;

(* Lean: southeast_first_shallow *)
let C983NRO_SOUTHEAST_FIRST_SHALLOW = prove
 (`forall c s u v a t h k.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t /\
     (&4 / &5) * t - c <= v /\ &0 < h /\ &0 <= k /\ k <= &9 / &41 /\ h pow 2 + k pow 2 = &1
     ==> &1 + (&4 / &5) * k - h < ABT_upper c s u v a k h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`; `h:real`; `k:real`]
    C983NRO_SOUTHEAST_FIRST_MINORANT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `ccntf_data c s u v a t` THEN REWRITE_TAC[ccntf_data; IMP_CONJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REPEAT DISCH_TAC THEN
  C983NRO_RING `c pow 2 + t pow 2 = &1` THEN
  C983NRO_PROD `&0 < h * c` THEN C983NRO_PROD `&0 <= k * t` THEN
  C983NRO_RING `(k * c - h * t) pow 2 + (h * c + k * t) pow 2 = &1` THEN
  MP_TAC(SPECL [`h * c + k * t`; `k * c - h * t`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(k * c - h * t) pow 2 + (h * c + k * t) pow 2 = &1` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  C983NRO_PROD `&0 <= (&9 / &41 - k) * (&9 / &41 + k)` THEN
  SUBGOAL_THEN `&40 / &41 <= h` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NRO_PROD `&0 < (&40 / &41 - h) * (&40 / &41 + h)` THEN C983NRO_LIN; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= k * c - h * t` THENL
   [C983NRO_RING `k * (h * c + k * t) - h * (k * c - h * t) = t` THEN
    C983NRO_PROD `&0 <= k * (&1 - (h * c + k * t))` THEN
    C983NRO_PROD `&0 <= h * (k * c - h * t)` THEN
    C983NRO_FACT `t <= k` THEN C983NRO_FACT `t <= &9 / &41` THEN
    C983NRO_PROD `&0 <= (&9 / &41 - t) * (&9 / &41 + t)` THEN
    SUBGOAL_THEN `&40 / &41 <= c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NRO_PROD `&0 < (&40 / &41 - c) * (&40 / &41 + c)` THEN C983NRO_LIN; ALL_TAC] THEN
    C983NRO_PROD `&0 <= (c - &40 / &41) * (c + &40 / &41 - &80 / &41)` THEN
    C983NRO_PROD `&0 <= (&9 / &41 - t) * (&18 / &41 - (&9 / &41 + t))` THEN
    C983NRO_FACT `c - &40 / &41 <= (&9 / &40) * (&9 / &41 - t)` THEN
    C983NRO_FACT `(&41 / &50) * (&9 / &41 - t) <= &1 - (&4 / &5) * c - t` THEN
    C983NRO_PROD `&0 <= (&9 / &41 - t) * (h + c - &80 / &41)` THEN
    C983NRO_PROD `&0 <= (h + c) * ((&1 - (&4 / &5) * c - t) - (&41 / &50) * (&9 / &41 - t))` THEN
    C983NRO_FACT `&0 <= (h + c) * (&1 - (&4 / &5) * c - t) - (k - t)` THEN
    C983NRO_RING `(&1 - (h * c + k * t)) * (h + c) = (k * c - h * t) * (k - t)` THEN
    C983NRO_PROD `&0 <= (k * c - h * t) * ((h + c) * (&1 - (&4 / &5) * c - t) - (k - t))` THEN
    SUBGOAL_THEN `&0 <= (k * c - h * t) * (&1 - (&4 / &5) * c - t) - (&1 - (h * c + k * t))`
      ASSUME_TAC THENL
     [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `h + c:real` THEN
      CONJ_TAC THEN C983NRO_LIN; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && is_binary "real_le" (lhand(concl th)) &&
      lhand(lhand(concl th)) = `&0` then MP_TAC th else failwith "") THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C983NRO_RING `(k * c - h * t) + (k * t + h * c) * (&1 + (&4 / &5) * t - c) -
                  (&1 + (&4 / &5) * k - h) =
                  (k * c - h * t) * (&1 - (&4 / &5) * c - t) - (&1 - (h * c + k * t))` THEN
    C983NRO_LIN;
    MP_TAC(SPECL [`c:real`; `t:real`; `h:real`; `k:real`] C983NRO_FIRST_STEEPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NRO_LIN; DISCH_TAC] THEN
    SUBGOAL_THEN `k * c - h * t <= &0` (fun th -> FIRST_X_ASSUM(MP_TAC o C MP th)) THENL
     [C983NRO_LIN; DISCH_TAC THEN C983NRO_LIN]]);;
let C983NRO_INPUT_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocrtd_input; ocrtd_rightprofile] o
    check (fun th -> can (term_match [] `ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR`) (concl th))) THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[ccntf_data] o
    check (fun th -> concl th = `ccntf_data cE sE uE vE aE (--sE)`)) THEN
  SUBGOAL_THEN `&1 < aN /\ &1 < aR` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cR pow 2 + (--sR) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING; ALL_TAC];;

(* Lean: first_bar_shallow_impossible *)
let C983NRO_FIRST_BAR_SHALLOW_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     (&4 / &5) * (--sE) - cE <= vE /\ --sR <= &9 / &41 /\
     ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR /\
     ABT_upper cE sE uE vE aE (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C983NRO_INPUT_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cR:real`; `--sR`]
    C983NRO_NORTH_SHALLOW_FLOOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NRO_LIN; REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`; `cR:real`; `--sR`]
    C983NRO_SOUTHEAST_FIRST_SHALLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NRO_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SPECL [`cR:real`; `--sR`; `uR:real`; `vR:real`; `aR:real`] OC983NWE_SHALLOW_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NRO_LIN);;

(* Lean: second_scalar (private) *)
let C983NRO_SECOND_SCALAR = prove
 (`forall c t h k.
     &0 < c /\ &0 < t /\ t <= c /\ &0 < h /\ &0 <= k /\
     c pow 2 + t pow 2 = &1 /\ h pow 2 + k pow 2 = &1
     ==> (&0 <= k * c - h * t
          ==> &1 - (&1 - k) / h <= (k * c - h * t) + (k * t + h * c) * (&1 - (&1 - t) / c)) /\
         (k * c - h * t <= &0
          ==> &1 - (&1 - k) / h <= (k * t + h * c) * (&1 - (&1 - t) / c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `e = (&1 - t) / c` THEN ABBREV_TAC `r = (&1 - k) / h` THEN
  SUBGOAL_THEN `c * e = &1 - t /\ h * r = &1 - k` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN EXPAND_TAC "r" THEN CONJ_TAC THEN MATCH_MP_TAC REAL_DIV_LMUL THEN
    C983NRO_LIN; ALL_TAC] THEN
  C983NRO_PROD `&0 < h * c` THEN C983NRO_PROD `&0 <= k * t` THEN
  C983NRO_RING `(k * c - h * t) pow 2 + (k * t + h * c) pow 2 = &1` THEN
  MP_TAC(SPECL [`k * t + h * c`; `k * c - h * t`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(k * c - h * t) pow 2 + (k * t + h * c) pow 2 = &1` THEN REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`] C983NRO_UNIT_LE) THEN
  MP_TAC(SPECL [`h:real`; `k:real`] C983NRO_UNIT_LE) THEN
  MP_TAC(SPECL [`k:real`; `h:real`] C983NRO_UNIT_LE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [UNDISCH_TAC `h pow 2 + k pow 2 = &1` THEN REAL_ARITH_TAC; REPEAT DISCH_TAC] THEN
  C983NRO_FACT `t <= &1` THEN
  SUBGOAL_THEN `&0 <= e /\ &0 <= r` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC C983NRO_NN_CANCEL THENL
     [EXISTS_TAC `c:real`; EXISTS_TAC `h:real`] THEN ASM_REWRITE_TAC[] THEN C983NRO_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + t) * e = c` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `forall c x y. &0 < c /\ c * (x - y) = &0 ==> x = y`) THEN
    EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c * e = &1 - t` THEN UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 + k) * r = h` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_FIELD `forall c x y. &0 < c /\ c * (x - y) = &0 ==> x = y`) THEN
    EXISTS_TAC `h:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `h * r = &1 - k` THEN UNDISCH_TAC `h pow 2 + k pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THENL
   [C983NRO_RING `k * (k * t + h * c) - h * (k * c - h * t) = t` THEN
    C983NRO_RING `h * (k * t + h * c) + k * (k * c - h * t) = c` THEN
    C983NRO_PROD `&0 <= k * (&1 - (k * t + h * c))` THEN
    C983NRO_PROD `&0 <= h * (k * c - h * t)` THEN
    C983NRO_FACT `t <= k` THEN
    C983NRO_PROD `&0 <= (k - t) * (t + k)` THEN
    SUBGOAL_THEN `h <= c` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NRO_PROD `&0 < (h - c) * (h + c)` THEN C983NRO_LIN; ALL_TAC] THEN
    C983NRO_PROD `&0 <= h * (&1 - (k * t + h * c))` THEN
    C983NRO_PROD `&0 <= (k * c - h * t) * (&1 - k)` THEN
    C983NRO_RING `c * h * (e - r) = h - c + (k * c - h * t)` THEN
    SUBGOAL_THEN `&0 <= e - r` ASSUME_TAC THENL
     [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `c * h:real` THEN
      CONJ_TAC THENL [C983NRO_LIN; REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN C983NRO_LIN];
      ALL_TAC] THEN
    C983NRO_RING `(k * c - h * t) + (k * t + h * c) * (&1 - e) - (&1 - r) =
                  (c - h) * r + (&1 - c) * k * (e - r)` THEN
    C983NRO_PROD `&0 <= (c - h) * r` THEN
    C983NRO_PROD `&0 <= (&1 - c) * k` THEN
    C983NRO_PROD `&0 <= ((&1 - c) * k) * (e - r)` THEN
    C983NRO_LIN;
    MP_TAC(SPECL [`k * t + h * c`; `--(k * c - h * t)`] C983NRO_UNIT_SUM) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY C983NRO_LIN THEN
      UNDISCH_TAC `(k * c - h * t) pow 2 + (k * t + h * c) pow 2 = &1` THEN
      CONV_TAC REAL_RING; DISCH_TAC] THEN
    MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NRO_LIN; STRIP_TAC] THEN
    SUBGOAL_THEN `e <= &1` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NRO_PROD `&0 < c * (e - &1)` THEN C983NRO_LIN; ALL_TAC] THEN
    C983NRO_FACT `(&1 + t) * (&1 - e) <= &1` THEN
    C983NRO_RING `(&1 + t) * (r - e) = --(k * c - h * t) + r * (&1 - (k * t + h * c))` THEN
    C983NRO_PROD `&0 <= r * (&1 - (k * t + h * c))` THEN
    C983NRO_PROD `&0 <= (&1 - (k * t + h * c)) * (&1 - (&1 + t) * (&1 - e))` THEN
    C983NRO_PROD `&0 <= (k * t + h * c) * --(k * c - h * t)` THEN
    SUBGOAL_THEN `&0 <= (&1 + t) * ((k * t + h * c) * (&1 - e) - (&1 - r))` ASSUME_TAC THENL
     [C983NRO_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (k * t + h * c) * (&1 - e) - (&1 - r)` MP_TAC THENL
     [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `&1 + t` THEN
      ASM_REWRITE_TAC[] THEN C983NRO_LIN; REAL_ARITH_TAC]]);;
(* Lean: southeast_second_floor *)
let C983NRO_SOUTHEAST_SECOND_FLOOR = prove
 (`forall c s u v a t h k.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t /\
     --(&1) <= --t * (u + a) + c * v /\ &0 < h /\ &0 <= k /\ h pow 2 + k pow 2 = &1
     ==> &1 - (&1 - k) / h < ABT_upper c s u v a k h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `ccntf_data c s u v a t` THEN REWRITE_TAC[ccntf_data; IMP_CONJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REPEAT DISCH_TAC THEN
  C983NRO_RING `c pow 2 + t pow 2 = &1` THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `h:real`; `k:real`] C983NRO_SECOND_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `e = (&1 - t) / c` THEN
  SUBGOAL_THEN `c * e = &1 - t` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C983NRO_LIN; ALL_TAC] THEN
  C983NRO_PROD `&0 < h * c` THEN C983NRO_PROD `&0 <= k * t` THEN
  C983NRO_PROD `&0 <= (k * t + h * c) * (&1 - t * (u + a) + c * v)` THEN
  C983NRO_PROD `&0 <= k * u` THEN
  ASM_CASES_TAC `&0 <= k * c - h * t` THENL
   [MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `k:real`; `h:real`]
      C983NRO_UPPER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C983NRO_LIN; DISCH_THEN SUBST1_TAC] THEN
    C983NRO_PROD `&0 < c * (k * t + h * c)` THEN
    C983NRO_PROD `&0 < (k + c * (k * t + h * c)) * (a - &1)` THEN
    C983NRO_RING `c * ((k * c - h * t) * (u + a) + (k * t + h * c) * (v + a)) =
                  k * u + (k + c * (k * t + h * c)) * a - (k * t + h * c) +
                  (k * t + h * c) * (&1 - t * (u + a) + c * v)` THEN
    C983NRO_RING `c * ((k * c - h * t) + (k * t + h * c) * (&1 - e)) =
                  k + c * (k * t + h * c) - (k * t + h * c)` THEN
    SUBGOAL_THEN `(k * c - h * t) + (k * t + h * c) * (&1 - e) <
                  (k * c + h * --t) * (u + a) + (--k * --t + h * c) * (v + a)`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC C983NRO_POS_CANCEL THEN
      EXISTS_TAC `c:real` THEN CONJ_TAC THEN C983NRO_LIN; ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `&0 <= k * c - h * t`
      then MP_TAC th else failwith "") THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C983NRO_LIN;
    MP_TAC(SPECL [`c:real`; `--t`; `u:real`; `v:real`; `a:real`; `k:real`; `h:real`]
      C983NRO_UPPER_IN_BANDS_NP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C983NRO_LIN; DISCH_THEN SUBST1_TAC] THEN
    C983NRO_PROD `&0 < (k * t + h * c) * (c + t)` THEN
    C983NRO_PROD `&0 < ((k * t + h * c) * (c + t)) * (a - &1)` THEN
    C983NRO_RING `c * ((k * c - h * t) * u + (k * t + h * c) * (v + a)) =
                  k * u + (k * t + h * c) * ((c + t) * a - &1) +
                  (k * t + h * c) * (&1 - t * (u + a) + c * v)` THEN
    C983NRO_RING `c * ((k * t + h * c) * (&1 - e)) = (k * t + h * c) * (c + t - &1)` THEN
    SUBGOAL_THEN `(k * t + h * c) * (&1 - e) <
                  (k * c + h * --t) * u + (--k * --t + h * c) * (v + a)`
      ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC C983NRO_POS_CANCEL THEN
      EXISTS_TAC `c:real` THEN CONJ_TAC THEN C983NRO_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `k * c - h * t <= &0` (fun th ->
      FIRST_X_ASSUM(MP_TAC o C MP th o check (fun th' -> is_imp(concl th') &&
        lhand(concl th') = `k * c - h * t <= &0`))) THENL
     [C983NRO_LIN; DISCH_TAC THEN C983NRO_LIN]]);;

(* Lean: wall_of_floors (private) *)
let C983NRO_WALL_OF_FLOORS = prove
 (`forall cN sN uN vN aN cE sE uE vE aE cR sR uR vR aR.
     cN * cN + sN * sN = &1 /\ &0 < aN /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\ &1 < aR /\
     ocrtd_rightprofile cR sR uR vR aR /\
     &1 - --sR < ABT_upper cN sN uN vN aN cR sR /\
     &1 - (&1 - --sR) / cR < ABT_upper cE sE uE vE aE (--sR) cR /\
     ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR /\
     ABT_upper cE sE uE vE aE (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ocrtd_rightprofile] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ABBREV_TAC `r = (&1 - --sR) / cR` THEN
  SUBGOAL_THEN `cR * r = &1 - --sR` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C983NRO_LIN; ALL_TAC] THEN
  C983NRO_PROD `&0 < cR * (vR - (&1 - r))` THEN
  MATCH_MP_TAC(SPECL [`cR:real`; `--sR`; `uR:real`; `vR:real`; `aR:real`] OC983NWE_UNIVERSAL_IMPOSSIBLE) THEN
  REPEAT CONJ_TAC THEN TRY C983NRO_LIN THEN
  UNDISCH_TAC `cR * cR + sR * sR = &1` THEN CONV_TAC REAL_RING);;

(* Lean: threshold_phase (private) *)
let C983NRO_THRESHOLD_PHASE = prove
 (`forall h k. &0 < h /\ &0 <= k /\ h pow 2 + k pow 2 = &1 /\ &9 / &41 <= k
         ==> &1 <= k + (&4 / &5) * h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:real`; `h:real`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL [UNDISCH_TAC `h pow 2 + k pow 2 = &1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  C983NRO_PROD `&0 <= (&41 * k - &9) * (&1 - k)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C983NRO_PROD `&0 < (&1 - (k + (&4 / &5) * h)) * (&1 - k + (&4 / &5) * h)` THEN
  C983NRO_LIN);;

(* Lean: threshold_floors (private) *)
let C983NRO_THRESHOLD_FLOORS = prove
 (`forall h k. &0 < h /\ &0 <= k /\ h pow 2 + k pow 2 = &1 /\ &9 / &41 <= k
         ==> &1 - (&1 - k) / h <= &1 + (&4 / &5) * k - h /\
             &1 - (&1 - k) / h <= k - h / &50`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `r = (&1 - k) / h` THEN
  SUBGOAL_THEN `h * r = &1 - k` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C983NRO_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`k:real`; `h:real`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL [UNDISCH_TAC `h pow 2 + k pow 2 = &1` THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  C983NRO_PROD `&0 <= (k - &9 / &41) * (k + &9 / &41)` THEN
  SUBGOAL_THEN `h <= &40 / &41` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NRO_PROD `&0 < (h - &40 / &41) * (h + &40 / &41)` THEN C983NRO_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`h:real`; `k:real`] C983NRO_THRESHOLD_PHASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  CONJ_TAC THENL
   [C983NRO_PROD `&0 <= k * ((k + (&4 / &5) * h) - &1)` THEN
    C983NRO_RING `h * ((&1 + (&4 / &5) * k - h) - (&1 - r)) = k * (k + (&4 / &5) * h - &1)` THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN MATCH_MP_TAC C983NRO_NN_CANCEL THEN
    EXISTS_TAC `h:real` THEN CONJ_TAC THEN C983NRO_LIN;
    C983NRO_PROD `&0 <= (k - &9 / &41) * (&50 * (k + &9 / &41) - (&1 + &40 / &41))` THEN
    C983NRO_PROD `&0 <= (&1 + k) * (&40 / &41 - h)` THEN
    C983NRO_FACT `&0 <= &50 * k pow 2 - (&1 + k) * (&1 + h)` THEN
    C983NRO_PROD `&0 <= h pow 2 * (&50 * k pow 2 - (&1 + k) * (&1 + h))` THEN
    C983NRO_RING `(&1 + k) * (&1 + h) * (&50 * (&1 - h) * (&1 - k) - h pow 2) =
                  h pow 2 * (&50 * k pow 2 - (&1 + k) * (&1 + h))` THEN
    C983NRO_PROD `&0 < (&1 + k) * (&1 + h)` THEN
    SUBGOAL_THEN `&0 <= &50 * (&1 - h) * (&1 - k) - h pow 2` ASSUME_TAC THENL
     [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `(&1 + k) * (&1 + h)` THEN
      CONJ_TAC THEN C983NRO_LIN; ALL_TAC] THEN
    C983NRO_RING `h * (k - h / &50 - (&1 - r)) = (&1 - h) * (&1 - k) - h pow 2 / &50` THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN MATCH_MP_TAC C983NRO_NN_CANCEL THEN
    EXISTS_TAC `h:real` THEN CONJ_TAC THEN C983NRO_LIN]);;

(* Lean: first_fixed_vertex (private) *)
let C983NRO_FIRST_FIXED_VERTEX = prove
 (`forall c t. &0 < c /\ &0 < t /\ t <= c /\ c pow 2 + t pow 2 = &1 /\ t <= &9 / &41
     ==> &1 <= c + t * (&1 + (&4 / &5) * t - c) /\
         &1 / &5 <= (&9 / &41) * (c + t * (&1 + (&4 / &5) * t - c)) +
                    (&40 / &41) * (--t + c * (&1 + (&4 / &5) * t - c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NRO_LIN; STRIP_TAC] THEN
  C983NRO_PROD `&0 <= (&9 / &41 - t) * (&9 / &41 + t)` THEN
  SUBGOAL_THEN `&40 / &41 <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NRO_PROD `&0 < (&40 / &41 - c) * (&40 / &41 + c)` THEN C983NRO_LIN; ALL_TAC] THEN
  C983NRO_RING `((&40 * c + &9 * t) / &41) pow 2 + ((&40 * t - &9 * c) / &41) pow 2 = &1` THEN
  MP_TAC(SPECL [`(&40 * c + &9 * t) / &41`; `(&40 * t - &9 * c) / &41`] C983NRO_UNIT_LE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  C983NRO_PROD `&0 <= (&1 - (&40 * c + &9 * t) / &41) *
                      ((&4 / &5) * ((&40 * c + &9 * t) / &41) - &1 / &5 - (&40 * t - &9 * c) / &41)` THEN
  C983NRO_RING `(&9 / &41) * (c + t * (&1 + (&4 / &5) * t - c)) +
                (&40 / &41) * (--t + c * (&1 + (&4 / &5) * t - c)) - &1 / &5 =
                (&1 - (&40 * c + &9 * t) / &41) *
                ((&4 / &5) * ((&40 * c + &9 * t) / &41) - &1 / &5 - (&40 * t - &9 * c) / &41)` THEN
  C983NRO_PROD `&0 <= (&1 - c) * ((&4 / &5) * c + t - &1 / &5)` THEN
  C983NRO_RING `(c + t * (&1 + (&4 / &5) * t - c)) - &1 = (&1 - c) * ((&4 / &5) * c + t - &1 / &5)` THEN
  CONJ_TAC THEN C983NRO_LIN);;
(* Lean: southeast_first_steep *)
let C983NRO_SOUTHEAST_FIRST_STEEP = prove
 (`forall c s u v a t h k.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t /\
     (&4 / &5) * t - c <= v /\ &0 < h /\ &0 <= k /\ &9 / &41 <= k /\ h pow 2 + k pow 2 = &1
     ==> &1 - (&1 - k) / h < ABT_upper c s u v a k h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`; `h:real`; `k:real`]
    C983NRO_SOUTHEAST_FIRST_MINORANT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`h:real`; `k:real`] C983NRO_THRESHOLD_FLOORS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  UNDISCH_TAC `ccntf_data c s u v a t` THEN REWRITE_TAC[ccntf_data; IMP_CONJ] THEN
  DISCH_THEN SUBST_ALL_TAC THEN REPEAT DISCH_TAC THEN
  C983NRO_RING `c pow 2 + t pow 2 = &1` THEN
  C983NRO_PROD `&0 < h * c` THEN C983NRO_PROD `&0 <= k * t` THEN
  ASM_CASES_TAC `&0 <= k * c - h * t` THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `&0 <= k * c - h * t`
      then MP_TAC th else failwith "") THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `t <= &9 / &41` THENL
     [MP_TAC(SPECL [`c:real`; `t:real`] C983NRO_FIRST_FIXED_VERTEX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      C983NRO_PROD `&0 <= (k - &9 / &41) * (k + &9 / &41)` THEN
      SUBGOAL_THEN `h <= &40 / &41` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        C983NRO_PROD `&0 < (h - &40 / &41) * (h + &40 / &41)` THEN C983NRO_LIN; ALL_TAC] THEN
      C983NRO_PROD `&0 <= (k - (&9 / &40) * h) * ((c + t * (&1 + (&4 / &5) * t - c)) - &1)` THEN
      C983NRO_PROD `&0 <= h * (((&9 / &41) * (c + t * (&1 + (&4 / &5) * t - c)) +
                    (&40 / &41) * (--t + c * (&1 + (&4 / &5) * t - c))) - &1 / &5)` THEN
      C983NRO_LIN;
      RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
      MP_TAC(SPECL [`c:real`; `t:real`] C983NRO_THRESHOLD_PHASE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NRO_LIN; DISCH_TAC] THEN
      C983NRO_PROD `&0 <= t * ((t + (&4 / &5) * c) - &1)` THEN
      MP_TAC(SPECL [`c:real`; `t:real`; `h:real`; `k:real`] C983NRO_SECOND_SCALAR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `&0 <= k * c - h * t`
        then MP_TAC th else failwith "") THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `e = (&1 - t) / c` THEN DISCH_TAC THEN
      SUBGOAL_THEN `c * e = &1 - t` ASSUME_TAC THENL
       [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C983NRO_LIN; ALL_TAC] THEN
      C983NRO_RING `c * ((&1 + (&4 / &5) * t - c) - (&1 - e)) = t * (t + (&4 / &5) * c - &1)` THEN
      SUBGOAL_THEN `&0 <= (&1 + (&4 / &5) * t - c) - (&1 - e)` ASSUME_TAC THENL
       [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `c:real` THEN
        CONJ_TAC THEN C983NRO_LIN; ALL_TAC] THEN
      C983NRO_PROD `&0 <= (k * t + h * c) * ((&1 + (&4 / &5) * t - c) - (&1 - e))` THEN
      C983NRO_LIN];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `k * c - h * t <= &0`
      then MP_TAC th else failwith "") THEN
    ANTS_TAC THENL [C983NRO_LIN; DISCH_TAC] THEN
    MP_TAC(SPECL [`c:real`; `t:real`; `h:real`; `k:real`] C983NRO_FIRST_STEEPER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NRO_LIN; DISCH_TAC] THEN
    C983NRO_LIN]);;

(* Lean: second_bar_impossible *)
let C983NRO_SECOND_BAR_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     --(&1) <= --(--sE) * (uE + aE) + cE * vE /\
     ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR /\
     ABT_upper cE sE uE vE aE (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C983NRO_INPUT_TAC THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] OCNTNS_RIGHT_AXIS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ocrtd_rightprofile]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cR:real`; `--sR`]
    C983NRO_NORTH_FLOOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NRO_LIN; REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`; `cR:real`; `--sR`]
    C983NRO_SOUTHEAST_SECOND_FLOOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NRO_LIN; DISCH_TAC] THEN
  MATCH_MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                      `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                      `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C983NRO_WALL_OF_FLOORS) THEN
  ASM_REWRITE_TAC[ocrtd_rightprofile]);;

(* Lean: impossible *)
let C983NRO_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR /\
     ABT_upper cE sE uE vE aE (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&4 / &5) * (--sE) - cE <= vE \/ --(&1) <= --(--sE) * (uE + aE) + cE * vE`
    MP_TAC THENL
   [UNDISCH_TAC `ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR` THEN
    SIMP_TAC[ocrtd_input; ccntf_data]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [ASM_CASES_TAC `--sR <= &9 / &41` THENL
     [MATCH_MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                          `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                          `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
        C983NRO_FIRST_BAR_SHALLOW_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    C983NRO_INPUT_TAC THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] OCNTNS_RIGHT_AXIS_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ocrtd_rightprofile]; STRIP_TAC] THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cR:real`; `--sR`]
      C983NRO_NORTH_FLOOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NRO_LIN; REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`; `cR:real`; `--sR`]
      C983NRO_SOUTHEAST_FIRST_STEEP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NRO_LIN; DISCH_TAC] THEN
    MATCH_MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                        `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C983NRO_WALL_OF_FLOORS) THEN
    ASM_REWRITE_TAC[ocrtd_rightprofile];
    MATCH_MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                        `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                        `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
      C983NRO_SECOND_BAR_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]]);;

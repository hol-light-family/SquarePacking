(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeIncoming.lean (Jatloe, N12-jatloe;*)
(* namespace N12Compact.CentralNegativeIncoming).  The reversed order for   *)
(* two negative canonical central frames is controlled by the actual lower  *)
(* crosspoint (2,1.5).  Normal is c977cc_normal; lower is ABT_lower,         *)
(* lower_in_bands C977NCO_LOWER_IN_BANDS.  A square B with B.s = -t is       *)
(* c s u v a with the hypothesis s = --t.  The Lean local abbreviations X, Y *)
(* are variables with their defining equations; K, H are written out.        *)
(* Tag CNI_.                                                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let CNI_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let CNI_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC];;

(* Lean: margin (private) *)
let CNI_MARGIN = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t /\ C * t <= S * c
     ==> C * ((&1 - c) * (&1 + t)) + S * (&1 / &2 - c - t - t pow 2) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CNI_NORMAL_TAC THEN
  SUBGOAL_THEN `exists X. X = (&1 - c) * (&1 + t)` (X_CHOOSE_TAC `X:real`) THENL
  [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `exists Y. Y = &1 / &2 - c - t - t pow 2` (X_CHOOSE_TAC `Y:real`) THENL
  [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c * X + t * Y = c - &1 - t / &2` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN `X + Y = (&1 - c) pow 2 - &1 / &2 - c * t` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  CNI_PROD_TAC `&1 - c` `c - &7 / &10` THEN
  CNI_PROD_TAC `c:real` `t:real` THEN
  SUBGOAL_THEN `X + Y <= &0` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `C * X + S * Y <= &0` MP_TAC THENL
  [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `c:real = t` THENL
  [SUBGOAL_THEN `C:real = S` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `c:real = t`)) THEN
    SUBGOAL_THEN `C <= S` ASSUME_TAC THENL [NLIN_TAC []; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `C:real = S`)) THEN
   CNI_PROD_TAC `C:real` `--(X + Y)` THEN NLIN_TAC ~deg2:false [];
   SUBGOAL_THEN `&0 < c - t` ASSUME_TAC THENL
   [UNDISCH_TAC `~(c:real = t)` THEN UNDISCH_TAC `t <= c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   CNI_PROD_TAC `C - S` `&1 + t / &2 - c` THEN
   CNI_PROD_TAC `S * c - C * t` `--(X + Y)` THEN
   SUBGOAL_THEN `(c - t) * (C * X + S * Y) =
                 (C - S) * (c - &1 - t / &2) + (S * c - C * t) * (X + Y)` ASSUME_TAC THENL
   [UNDISCH_TAC `c * X + t * Y = c - &1 - t / &2` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `(c - t) * (C * X + S * Y) <= &0` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`c - t`; `C * X + S * Y`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ASM_REAL_ARITH_TAC]]);;

(* Lean: lower_bound *)
let CNI_LOWER_BOUND = prove
 (`forall c s u v a t C S.
     c * c + s * s = &1 /\ &0 < a /\
     s = --t /\ c977cc_normal C S /\ c977cc_normal c t /\ &1 <= a /\
     C * t <= S * c /\ c + &3 * t <= v /\ u + a <= &3 * c - &2 * t
     ==> ABT_lower c s u v a C (--S) <= &2 * C - (&3 / &2) * S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `c:real`; `t:real`] CNI_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  CNI_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= C * c + S * t` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C * t - S * c <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower c (--t) u v a C (--S) =
                (C * c + S * t) * u + (C * t - S * c) * (v + a)` SUBST1_TAC THENL
  [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   REWRITE_TAC[REAL_ARITH `C * c + --S * --t = C * c + S * t`;
               REAL_ARITH `--C * --t + --S * c = C * t - S * c`] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  CNI_PROD_TAC `C * c + S * t` `(&3 * c - &2 * t) - (u + a)` THEN
  CNI_PROD_TAC `--(C * t - S * c)` `v - (c + &3 * t)` THEN
  CNI_PROD_TAC `(C * c + S * t) - (C * t - S * c)` `a - &1` THEN
  SUBGOAL_THEN
   `(C * c + S * t) * (&3 * c - &2 * t - &1) + (C * t - S * c) * (c + &3 * t + &1) -
    (&2 * C - (&3 / &2) * S) =
    C * ((&1 - c) * (&1 + t)) + S * (&1 / &2 - c - t - t pow 2)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

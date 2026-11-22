(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeIncomingBottom.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.CentralNegativeIncomingBottom).  The    *)
(* negative central test direction also excludes the upper-U miss of the    *)
(* farther actual bottom point.  Square B is c s u v a with s = --t; Normal  *)
(* is c977cc_normal; Lean `lower B C (-S)` is ABT_lower c s u v a C (--S)    *)
(* (lower_in_bands C977NCO_LOWER_IN_BANDS); negative_bands is                *)
(* C977NCO_NEGATIVE_BANDS.  The Lean abbreviations X, Y, K, H are written    *)
(* out.  Tag CNIB_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralNegativeBottomUpper.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/UpperRightNegativeTopBounds.ml";;
needs "n12/geometry/ABTransverse.ml";;

let CNIB_LIN = NLIN_TAC ~deg2:false [];;
let CNIB_PROD a b = CNBU_PROD_TAC a b;;
let CNIB_SQ x = MP_TAC(SPEC x REAL_LE_SQUARE) THEN DISCH_TAC;;
let CNIB_RING tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC];;

(* Lean: arc (private) *)
let CNIB_ARC = prove
 (`forall c t. c977cc_normal c t
     ==> &1 + (&7 / &10) * c * t <= c + t /\ t pow 2 <= &1 / &2 /\ c * t <= &1 / &2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN URNTB_NORMAL_TAC THEN
  CNIB_PROD `c + t - &1` `&1 - (&7 / &20) * (c + t + &1)` THEN
  CNIB_PROD `c - t` `c + t` THEN CNIB_PROD `c - t` `c - t` THEN
  REPEAT CONJ_TAC THEN CNIB_LIN);;

(* Lean: first_margin (private) *)
let CNIB_FIRST_MARGIN = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t /\ &0 <= C * t - S * c
     ==> C * (&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t) -
         S * (&1 / &2 - t pow 2 + (&2 / &5) * c * t + t - c) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CNIB_ARC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  URNTB_NORMAL_TAC THEN
  SUBGOAL_THEN `&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t <= &0` ASSUME_TAC THENL
   [CNIB_LIN; ALL_TAC] THEN
  CNIB_RING `S * (c * (&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t) -
             t * (&1 / &2 - t pow 2 + (&2 / &5) * c * t + t - c)) = S * ((&3 / &5) * c + t / &2 - &1)` THEN
  CNIB_SQ `c - &3 / &5` THEN CNIB_SQ `t - &1 / &2` THEN
  SUBGOAL_THEN `(&3 / &5) * c + t / &2 <= &1` ASSUME_TAC THENL [CNIB_LIN; ALL_TAC] THEN
  ASM_CASES_TAC `&0 < t` THENL
   [CNIB_PROD `C * t - S * c` `--(&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t)` THEN
    CNIB_PROD `S:real` `&1 - ((&3 / &5) * c + t / &2)` THEN
    SUBGOAL_THEN
     `t * (C * (&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t) -
           S * (&1 / &2 - t pow 2 + (&2 / &5) * c * t + t - c)) <= &0` ASSUME_TAC THENL
     [CNIB_LIN; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`t:real`;
      `C * (&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t) -
       S * (&1 / &2 - t pow 2 + (&2 / &5) * c * t + t - c)`] REAL_LT_MUL) THEN
    ASM_REWRITE_TAC[] THEN CNIB_LIN;
    SUBGOAL_THEN `t = &0` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THEN CNIB_LIN; ALL_TAC] THEN
    CNIB_PROD `S:real` `c:real` THEN
    SUBGOAL_THEN `S = &0` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`S:real`; `c:real`] REAL_LT_MUL) THEN ANTS_TAC THENL
         [CONJ_TAC THEN CNIB_LIN; DISCH_TAC THEN CNIB_LIN];
        CNIB_LIN];
      ALL_TAC] THEN
    CNIB_PROD `C:real` `--(&3 / &5 - c - &0 + (&2 / &5) * &0 pow 2 + c * &0)` THEN
    CNIB_LIN]);;

(* Lean: last_margin (private) *)
let CNIB_LAST_MARGIN = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t /\ C * t - S * c <= &0
     ==> C * (&3 / &5 - c - t pow 2 / &4 + (&13 / &20) * c * t) -
         S * (&3 / &20 - (&13 / &20) * t pow 2 - c * t / &4 + t) <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CNIB_ARC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  URNTB_NORMAL_TAC THEN
  CNIB_RING `(C - S) * (c * (&3 / &5 - c - t pow 2 / &4 + (&13 / &20) * c * t) -
             t * (&3 / &20 - (&13 / &20) * t pow 2 - c * t / &4 + t)) =
             (C - S) * ((&3 / &5) * c + t / &2 - &1)` THEN
  CNIB_SQ `c - &3 / &5` THEN CNIB_SQ `t - &1 / &2` THEN
  SUBGOAL_THEN `(&3 / &5) * c + t / &2 <= &1` ASSUME_TAC THENL [CNIB_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &5 - c - t pow 2 / &4 + (&13 / &20) * c * t) -
                (&3 / &20 - (&13 / &20) * t pow 2 - c * t / &4 + t) <= &0` ASSUME_TAC THENL
   [CNIB_LIN; ALL_TAC] THEN
  ASM_CASES_TAC `c:real = t` THENL
   [FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `C:real = S` SUBST_ALL_TAC THENL
     [REWRITE_TAC[GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
        MP_TAC(SPECL [`C - S`; `c:real`] REAL_LT_MUL) THEN ANTS_TAC THENL
         [CONJ_TAC THEN CNIB_LIN; DISCH_TAC THEN CNIB_LIN];
        CNIB_LIN];
      ALL_TAC] THEN
    CNIB_PROD `S:real` `--((&3 / &5 - c - c pow 2 / &4 + (&13 / &20) * c * c) -
                (&3 / &20 - (&13 / &20) * c pow 2 - c * c / &4 + c))` THEN
    CNIB_LIN;
    SUBGOAL_THEN `&0 < c - t` ASSUME_TAC THENL
     [UNDISCH_TAC `~(c:real = t)` THEN UNDISCH_TAC `t <= c` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CNIB_PROD `C - S` `&1 - ((&3 / &5) * c + t / &2)` THEN
    CNIB_PROD `S * c - C * t` `--((&3 / &5 - c - t pow 2 / &4 + (&13 / &20) * c * t) -
                (&3 / &20 - (&13 / &20) * t pow 2 - c * t / &4 + t))` THEN
    SUBGOAL_THEN
     `(c - t) * (C * (&3 / &5 - c - t pow 2 / &4 + (&13 / &20) * c * t) -
         S * (&3 / &20 - (&13 / &20) * t pow 2 - c * t / &4 + t)) <= &0` ASSUME_TAC THENL
     [CNIB_LIN; ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`c - t`;
      `C * (&3 / &5 - c - t pow 2 / &4 + (&13 / &20) * c * t) -
       S * (&3 / &20 - (&13 / &20) * t pow 2 - c * t / &4 + t)`] REAL_LT_MUL) THEN
    ASM_REWRITE_TAC[] THEN CNIB_LIN]);;

(* the lower support in direction (C, --S) for both signs of H (Lean formula) *)
let CNIB_FORMULA = prove
 (`forall c s u v a t C S.
     s = --t /\ &0 <= C * c + S * t
     ==> (&0 <= C * t - S * c
          ==> ABT_lower c s u v a C (--S) = (C * c + S * t) * u + (C * t - S * c) * v) /\
         (C * t - S * c <= &0
          ==> ABT_lower c s u v a C (--S) = (C * c + S * t) * u + (C * t - S * c) * (v + a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `C * c + --S * --t = C * c + S * t`;
              REAL_ARITH `--C * --t + --S * c = C * t - S * c`] THEN
  CONJ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_ARITH `x <= &0 ==> abs x = --x`] THEN
  REAL_ARITH_TAC);;

(* Lean: upper_u_impossible *)
let CNIB_UPPER_U_IMPOSSIBLE = prove
 (`forall c s u v a t C S.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C S /\ c977cc_normal c t /\ s = --t /\ &1 <= a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     u + a <= (&13 / &5) * c - t /\ v + a <= &2 * c + &3 * t /\
     &2 * C - (&3 / &2) * S < ABT_lower c s u v a C (--S)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN URNTB_NORMAL_TAC THEN
  CNIB_PROD `C:real` `c:real` THEN CNIB_PROD `S:real` `t:real` THEN
  SUBGOAL_THEN `&0 <= C * c + S * t` ASSUME_TAC THENL [CNIB_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`; `C:real`; `S:real`]
    CNIB_FORMULA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  CNIB_PROD `C * c + S * t` `((&13 / &5) * c - t) - (u + a)` THEN
  ASM_CASES_TAC `&0 <= C * t - S * c` THENL
   [FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `&0 <= C * t - S * c`
      then MP_TAC th else failwith "") THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`C:real`; `S:real`; `c:real`; `t:real`] CNIB_FIRST_MARGIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    CNIB_PROD `C * t - S * c` `(&2 * c + &3 * t) - (v + a)` THEN
    CNIB_PROD `(C * c + S * t) + (C * t - S * c)` `a - &1` THEN
    CNIB_RING `(C * c + S * t) * ((&13 / &5) * c - t - &1) +
               (C * t - S * c) * (&2 * c + &3 * t - &1) - (&2 * C - (&3 / &2) * S) =
               C * (&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t) -
               S * (&1 / &2 - t pow 2 + (&2 / &5) * c * t + t - c)` THEN
    CNIB_LIN;
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
    FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `C * t - S * c <= &0`
      then MP_TAC th else failwith "") THEN
    ANTS_TAC THENL [CNIB_LIN; DISCH_TAC] THEN
    MP_TAC(SPECL [`C:real`; `S:real`; `c:real`; `t:real`] CNIB_LAST_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CNIB_LIN; DISCH_TAC] THEN
    UNDISCH_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
    ASM_SIMP_TAC[C977NCO_NEGATIVE_BANDS] THEN STRIP_TAC THEN
    CNIB_PROD `--(C * t - S * c)` `(v + a) - ((&33 / &20) * c + (&47 / &20) * t)` THEN
    CNIB_PROD `C * c + S * t` `a - &1` THEN
    CNIB_RING `(C * c + S * t) * ((&13 / &5) * c - t - &1) +
               (C * t - S * c) * ((&33 / &20) * c + (&47 / &20) * t) - (&2 * C - (&3 / &2) * S) =
               C * (&3 / &5 - c - t pow 2 / &4 + (&13 / &20) * c * t) -
               S * (&3 / &20 - (&13 / &20) * t pow 2 - c * t / &4 + t)` THEN
    CNIB_LIN]);;

(* Lean: lower_face *)
let CNIB_LOWER_FACE = prove
 (`forall c s u v a t C S.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C S /\ c977cc_normal c t /\ s = --t /\ &1 <= a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     v + a <= &2 * c + &3 * t /\
     &2 * C - (&3 / &2) * S < ABT_lower c s u v a C (--S) /\
     ~linside c s u v a (&13 / &5) (&1)
     ==> c + (&13 / &5) * t <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `u + a <= (&13 / &5) * c - t` THENL
   [MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`;
                        `C:real`; `S:real`] CNIB_UPPER_U_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  URNTB_NORMAL_TAC THEN
  UNDISCH_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
  UNDISCH_TAC `~linside c s u v a (&13 / &5) (&1)` THEN
  ASM_SIMP_TAC[C977NCO_NEGATIVE_BANDS] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

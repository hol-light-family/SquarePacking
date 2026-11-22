(* ========================================================================= *)
(* Port of Compact/Geometry/CentralNegativeBottomUpper.lean (Jatloe,         *)
(* N12-jatloe; namespace N12Compact.CentralNegativeBottomUpper).  The       *)
(* upper-U escape of the actual bottom point cannot coexist with the missing *)
(* inward right point and an incoming positive central axis.  Square B is   *)
(* c s u v a with s = --t; Normal is c977cc_normal; lower is ABT_lower       *)
(* (lower_in_bands C977NCO_LOWER_IN_BANDS); negative_bands is                *)
(* C977NCO_NEGATIVE_BANDS; UpperRightNegativeTopBounds.arc is URNTB_ARC.     *)
(* The Lean abbreviations X, Y, K, H are written out.  Tag CNBU_.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralSteeperBottomReach.ml";;
needs "n12/geometry/UpperRightNegativeTopBounds.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;
needs "n12/geometry/ABTransverse.ml";;

let CNBU_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC];;

(* Lean: margin (private) *)
let CNBU_MARGIN = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t
     ==> (C * c - S * t) * ((&13 / &5) * c - t - &1) +
         (C * t + S * c) * (&2 * c + &3 * t - &1) <= &2 * (C + S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `t:real`] URNTB_ARC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN URNTB_NORMAL_TAC THEN
  CNBU_PROD_TAC `c - t` `c - t` THEN
  SUBGOAL_THEN `c * t <= &1 / &2` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNBU_PROD_TAC `c - t` `c + t` THEN
  SUBGOAL_THEN `t pow 2 <= &1 / &2` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNBU_PROD_TAC `t:real` `t:real` THEN
  SUBGOAL_THEN `&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t <= &0` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `(&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t) +
                (--(t pow 2) + (&2 / &5) * c * t - c + t) <= &0` ASSUME_TAC THENL
   [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  CNBU_PROD_TAC `C - S` `--(&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t)` THEN
  CNBU_PROD_TAC `S:real` `--((&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t) +
                (--(t pow 2) + (&2 / &5) * c * t - c + t))` THEN
  SUBGOAL_THEN
   `(C * c - S * t) * ((&13 / &5) * c - t - &1) +
    (C * t + S * c) * (&2 * c + &3 * t - &1) - &2 * (C + S) =
    C * (&3 / &5 - c - t + (&2 / &5) * t pow 2 + c * t) +
    S * (--(t pow 2) + (&2 / &5) * c * t - c + t)` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* the lower support in the positive-K, positive-H band (Lean formula) *)
let CNBU_FORMULA = prove
 (`forall c s u v a t C S.
     s = --t /\ &0 <= C * c - S * t /\ &0 <= C * t + S * c
     ==> ABT_lower c s u v a C S = (C * c - S * t) * u + (C * t + S * c) * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
  REWRITE_TAC[REAL_ARITH `C * c + S * --t = C * c - S * t`;
              REAL_ARITH `--C * --t + S * c = C * t + S * c`] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC);;

(* Lean: upper_u_impossible *)
let CNBU_UPPER_U_IMPOSSIBLE = prove
 (`forall c s u v a t C S.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C S /\ c977cc_normal c t /\ s = --t /\ &1 <= a /\
     u + a <= (&13 / &5) * c - t /\ v + a <= &2 * c + &3 * t /\
     &2 * (C + S) < ABT_lower c s u v a C S
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `c:real`; `t:real`] CNBU_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN URNTB_NORMAL_TAC THEN
  CNBU_PROD_TAC `c:real` `C - S` THEN CNBU_PROD_TAC `S:real` `c - t` THEN
  CNBU_PROD_TAC `C:real` `t:real` THEN CNBU_PROD_TAC `S:real` `c:real` THEN
  SUBGOAL_THEN `&0 <= C * c - S * t /\ &0 <= C * t + S * c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`; `C:real`; `S:real`]
    CNBU_FORMULA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  CNBU_PROD_TAC `C * c - S * t` `(&13 / &5) * c - t - &1 - u` THEN
  CNBU_PROD_TAC `C * t + S * c` `&2 * c + &3 * t - &1 - v` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lower_face *)
let CNBU_LOWER_FACE = prove
 (`forall c s u v a t C S.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C S /\ c977cc_normal c t /\ s = --t /\ &1 <= a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     v + a <= &2 * c + &3 * t /\
     &2 * (C + S) < ABT_lower c s u v a C S /\
     ~linside c s u v a (&13 / &5) (&1)
     ==> c + (&13 / &5) * t <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `u + a <= (&13 / &5) * c - t` THENL
   [MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`;
                        `C:real`; `S:real`] CNBU_UPPER_U_IMPOSSIBLE) THEN
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

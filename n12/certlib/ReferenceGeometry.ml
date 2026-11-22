(* ========================================================================= *)
(* Port of source/S12/ReferenceGeometry.lean (Jatloe, N12-jatloe).           *)
(* (Its import CornerCover is not used by this file.)                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/OverlapCertificate.ml";;

(* Lean: strict_abs_linear_bound *)
let RG_STRICT_ABS_LINEAR_BOUND = prove
 (`forall A B x y r. abs x < r /\ abs y < r /\ &0 < abs A + abs B
     ==> abs(A * x + B * y) < (abs A + abs B) * r`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `abs A * abs x + abs B * abs y` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM REAL_ABS_MUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN
  MP_TAC(SPEC `A:real` REAL_ABS_POS) THEN MP_TAC(SPEC `B:real` REAL_ABS_POS) THEN
  MP_TAC(SPEC `x:real` REAL_ABS_POS) THEN MP_TAC(SPEC `y:real` REAL_ABS_POS) THEN
  SPEC_TAC(`abs A`,`a:real`) THEN SPEC_TAC(`abs B`,`b:real`) THEN
  SPEC_TAC(`abs x`,`p:real`) THEN SPEC_TAC(`abs y`,`q:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASM_CASES_TAC `p <= q` THEN NLIN_TAC []);;

let RG_ABS_LT = REAL_ARITH `forall x h. abs x < h <=> --h < x /\ x < h`;;

(* Lean: normal_change_inner *)
let RG_NORMAL_CHANGE_INNER = prove
 (`forall c s u v a b x y.
     c pow 2 + s pow 2 = &1 /\ u pow 2 + v pow 2 = &1 /\ &0 < b /\
     b * (abs(c * u + s * v) + abs(--c * v + s * u)) <= a /\
     abs(u * x + v * y) < b / &2 /\ abs(--v * x + u * y) < b / &2
     ==> abs(c * x + s * y) < a / &2 /\ abs(--s * x + c * y) < a / &2`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `D = c * u + s * v` THEN ABBREV_TAC `E = --c * v + s * u` THEN STRIP_TAC THEN
  SUBGOAL_THEN `D pow 2 + E pow 2 = &1` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["D"; "E"] THEN
    UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN UNDISCH_TAC `u pow 2 + v pow 2 = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < abs D + abs E` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `D = &0 /\ E = &0` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `D pow 2 + E pow 2 = &1` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c * x + s * y = D * (u * x + v * y) + E * (--v * x + u * y) /\
                --s * x + c * y = --E * (u * x + v * y) + D * (--v * x + u * y)`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [MAP_EVERY EXPAND_TAC ["D"; "E"] THEN CONJ_TAC THEN
    UNDISCH_TAC `u pow 2 + v pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`D:real`; `E:real`; `u * x + v * y`; `--v * x + u * y`; `b / &2`]
    RG_STRICT_ABS_LINEAR_BOUND) THEN
  MP_TAC(SPECL [`--E:real`; `D:real`; `u * x + v * y`; `--v * x + u * y`; `b / &2`]
    RG_STRICT_ABS_LINEAR_BOUND) THEN
  ASM_REWRITE_TAC[REAL_ABS_NEG] THEN
  REPEAT(ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
  REPEAT DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: reference_inner_containment *)
let RG_REFERENCE_INNER_CONTAINMENT = prove
 (`forall c s u v a r.
     c * c + s * s = &1 /\ &0 < a /\ rs_check r /\
     rs_side r * (abs(c * rs_c r + s * rs_s r) + abs(--c * rs_s r + s * rs_c r)) <= a
     ==> forall P. psub P (lcx c s u v a, lcy c s u v a) IN rs_sqset r ==> P IN sqset c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `P:real#real` THEN
  REWRITE_TAC[rs_sqset; IN_SQSET; psub; linside] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `rs_c r`; `rs_s r`; `a:real`; `rs_side r`;
                `FST(P:real#real) - lcx c s u v a`; `SND(P:real#real) - lcy c s u v a`]
    RG_NORMAL_CHANGE_INNER) THEN
  UNDISCH_TAC `rs_check r` THEN REWRITE_TAC[rs_check] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[REAL_POW_2; RG_ABS_LT] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

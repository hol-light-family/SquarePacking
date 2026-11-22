(* ========================================================================= *)
(* Port of Compact/Geometry/C1092ShallowPositiveScalars.lean (Jatloe).        *)
(* Exact half-angle versions of the C1092 shallow-positive wall scalars:     *)
(* cosH x = (1-x^2)/(1+x^2), sinH x = 2x/(1+x^2).  The rational identities   *)
(* are checked by REAL_FIELD; the signs come from                            *)
(* C1092ShallowPositiveScalarsPolynomials.                                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C1092ShallowPositiveScalarsPolynomials.ml";;

(* Lean: cosH, sinH, relativeCos, relativeSin, scalarB, wallWeight, wallDen,
   leftPlus, leftMinus, bottomMinus, bottomSlope (definitions) *)
let c1092sps_cosH = new_definition `c1092sps_cosH (x:real) = (&1 - x pow 2) / (&1 + x pow 2)`;;
let c1092sps_sinH = new_definition `c1092sps_sinH (x:real) = (&2 * x) / (&1 + x pow 2)`;;
let c1092sps_relCos = new_definition
 `c1092sps_relCos (x:real) (z:real) =
    c1092sps_cosH x * c1092sps_cosH z + c1092sps_sinH x * c1092sps_sinH z`;;
let c1092sps_relSin = new_definition
 `c1092sps_relSin (x:real) (z:real) =
    c1092sps_cosH x * c1092sps_sinH z - c1092sps_sinH x * c1092sps_cosH z`;;
let c1092sps_scalarB = new_definition
 `c1092sps_scalarB (a:real) (x:real) =
    a * (&3 / &2 + (c1092sps_cosH x * (c1092sps_cosH x + c1092sps_sinH x)) / &2)`;;
let c1092sps_wallWeight = new_definition
 `c1092sps_wallWeight (z:real) =
    &1 + c1092sps_sinH z pow 2 + c1092sps_sinH z * c1092sps_cosH z`;;
let c1092sps_wallDen = new_definition
 `c1092sps_wallDen (x:real) (z:real) =
    x * (&1 + x pow 2) * (&1 + z pow 2) pow 2 * (&1 + x * z - x + z) * (&1 + x * z + x - z)`;;
let c1092sps_leftPlus = new_definition
 `c1092sps_leftPlus (a:real) (x:real) (z:real) =
    c1092sps_cosH z / c1092sps_sinH x *
      (c1092sps_scalarB a x - &2 * c1092sps_cosH x -
       (c1092sps_sinH z - c1092sps_relSin x z * (a + c1092sps_sinH x / &2)) /
       c1092sps_relCos x z) -
    c1092sps_sinH z + (a * c1092sps_wallWeight z) / &2`;;
let c1092sps_leftMinus = new_definition
 `c1092sps_leftMinus (a:real) (x:real) (z:real) =
    c1092sps_cosH z / c1092sps_sinH x *
      (c1092sps_scalarB a x - &2 * c1092sps_cosH x -
       (c1092sps_sinH z + c1092sps_relSin x z * (a - c1092sps_cosH x - c1092sps_sinH x)) /
       c1092sps_relCos x z) -
    c1092sps_sinH z + (a * c1092sps_wallWeight z) / &2`;;
let c1092sps_bottomMinus = new_definition
 `c1092sps_bottomMinus (a:real) (x:real) (z:real) =
    (a * c1092sps_wallWeight z) / &2 +
    (a * ((c1092sps_cosH x + c1092sps_sinH x) / &2 - &1 / c1092sps_sinH x) +
     c1092sps_cosH x / c1092sps_sinH x - (&11 / &25) * c1092sps_cosH x pow 2) *
      c1092sps_cosH z +
    (--a * c1092sps_sinH x - &1 + (&11 / &25) * c1092sps_cosH x * c1092sps_sinH x) *
      c1092sps_sinH z`;;
let c1092sps_bottomSlope = new_definition
 `c1092sps_bottomSlope (x:real) (z:real) =
    c1092sps_wallWeight z / &2 +
    ((c1092sps_cosH x + c1092sps_sinH x) / &2 - &1 / c1092sps_sinH x) * c1092sps_cosH z -
    c1092sps_sinH x * c1092sps_sinH z`;;

(* positivity with divisions (Lean: positivity) *)
let rec C1092SPS_POS_TAC g =
  (FIRST
    [CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
     FIRST_ASSUM ACCEPT_TAC;
     FIRST_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP REAL_LT_IMP_LE th));
     MATCH_ACCEPT_TAC REAL_LE_POW_2;
     MATCH_ACCEPT_TAC REAL_LE_SQUARE;
     MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_LET_ADD THEN CONJ_TAC THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_POW_LT THEN C1092SPS_POS_TAC;
     MATCH_MP_TAC REAL_POW_LE THEN C1092SPS_POS_TAC]) g;;

let C1092SPS_DIV_LNEG = prove
 (`forall x y. --x / y = --(x / y)`,
  REWRITE_TAC[real_div; REAL_MUL_LNEG]);;

(* Lean: half_den_pos *)
let C1092SPS_HALF_DEN_POS = prove
 (`forall x. &0 < &1 + x pow 2`,
  GEN_TAC THEN MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC);;

let C1092SPS_HALF_DEN_NZ = prove
 (`forall x. ~(&1 + x pow 2 = &0)`,
  MESON_TAC[C1092SPS_HALF_DEN_POS; REAL_LT_IMP_NZ]);;

let C1092SPS_FIELD_TAC =
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_NZ) THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_NZ) THEN
  REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_FIELD;;

(* Lean: half_unit *)
let C1092SPS_HALF_UNIT = prove
 (`forall x. c1092sps_cosH x pow 2 + c1092sps_sinH x pow 2 = &1`,
  GEN_TAC THEN REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_NZ) THEN CONV_TAC REAL_FIELD);;

(* Lean: half_sin_pos *)
let C1092SPS_HALF_SIN_POS = prove
 (`forall x. &0 < x ==> &0 < c1092sps_sinH x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1092sps_sinH] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[C1092SPS_HALF_DEN_POS] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: half_cos_pos *)
let C1092SPS_HALF_COS_POS = prove
 (`forall x. &0 <= x /\ x < &1 ==> &0 < c1092sps_cosH x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c1092sps_cosH] THEN
  MATCH_MP_TAC REAL_LT_DIV THEN REWRITE_TAC[C1092SPS_HALF_DEN_POS] THEN
  NLIN_TAC []);;

(* Lean: relative_cos_factor *)
let C1092SPS_RELATIVE_COS_FACTOR = prove
 (`forall x z. c1092sps_relCos x z =
         ((&1 + x * z - x + z) * (&1 + x * z + x - z)) / ((&1 + x pow 2) * (&1 + z pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092sps_relCos; c1092sps_cosH; c1092sps_sinH] THEN
  C1092SPS_FIELD_TAC);;

(* Lean: relative_sin_factor *)
let C1092SPS_RELATIVE_SIN_FACTOR = prove
 (`forall x z. c1092sps_relSin x z =
         (&2 * (z - x) * (&1 + x * z)) / ((&1 + x pow 2) * (&1 + z pow 2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092sps_relSin; c1092sps_cosH; c1092sps_sinH] THEN
  C1092SPS_FIELD_TAC);;

(* Lean: wall_factors_pos *)
let C1092SPS_WALL_FACTORS_POS = prove
 (`forall x z. &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z < &1
         ==> &0 < &1 + x * z - x + z /\ &0 < &1 + x * z + x - z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x * z` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: relative_cos_pos *)
let C1092SPS_RELATIVE_COS_POS = prove
 (`forall x z. &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z < &1 ==> &0 < c1092sps_relCos x z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092SPS_WALL_FACTORS_POS) THEN
  REWRITE_TAC[C1092SPS_RELATIVE_COS_FACTOR] THEN
  REPEAT(MATCH_MP_TAC REAL_LT_DIV ORELSE MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
  ASM_REWRITE_TAC[C1092SPS_HALF_DEN_POS]);;

(* Lean: wall_den_pos *)
let C1092SPS_WALL_DEN_POS = prove
 (`forall x z. &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z < &1 ==> &0 < c1092sps_wallDen x z`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C1092SPS_WALL_FACTORS_POS) THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[c1092sps_wallDen] THEN STRIP_ASSUME_TAC(ASSUME
    `&0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z < &1`) THEN
  C1092SPS_POS_TAC);;

let C1092SPS_ONE_TAC polydefs =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SPS_WALL_FACTORS_POS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x = &0) /\ ~(&1 + x * z - x + z = &0) /\ ~(&1 + x * z + x - z = &0)`
  MP_TAC THENL [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN STRIP_TAC THEN
  REWRITE_TAC[c1092sps_leftPlus; c1092sps_leftMinus;
              C1092SPS_RELATIVE_COS_FACTOR; C1092SPS_RELATIVE_SIN_FACTOR] THEN
  REWRITE_TAC([c1092sps_scalarB; c1092sps_wallWeight; c1092sps_cosH; c1092sps_sinH;
               c1092sps_wallDen] @ polydefs) THEN
  C1092SPS_FIELD_TAC;;

(* Lean: left_plus_one *)
let C1092SPS_LEFT_PLUS_ONE = prove
 (`forall x z. &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z < &1
         ==> c1092sps_leftPlus (&1) x z =
             (x * (&1 - z) * c1092spsp_ascP x (z - x)) / c1092sps_wallDen x z`,
  C1092SPS_ONE_TAC [c1092spsp_ascP; c1092spsp_ascC0; c1092spsp_ascC1; c1092spsp_ascC2;
                    c1092spsp_ascC3; c1092spsp_ascC4; c1092spsp_ascC5]);;

(* Lean: left_minus_one *)
let C1092SPS_LEFT_MINUS_ONE = prove
 (`forall x z. &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z < &1
         ==> c1092sps_leftMinus (&1) x z =
             ((&1 - z) * c1092spsp_descP z (x - z)) / c1092sps_wallDen x z`,
  C1092SPS_ONE_TAC [c1092spsp_descP; c1092spsp_descE0; c1092spsp_descE1; c1092spsp_descE2;
                    c1092spsp_descE3; c1092spsp_descE4; c1092spsp_descE5;
                    c1092spsp_descE6]);;

(* Lean: left_plus_affine *)
let C1092SPS_LEFT_PLUS_AFFINE = prove
 (`forall a x z. c1092sps_leftPlus a x z =
     c1092sps_leftPlus (&1) x z + (a - &1) *
       (c1092sps_cosH z / c1092sps_sinH x *
          (&3 / &2 + (c1092sps_cosH x * (c1092sps_cosH x + c1092sps_sinH x)) / &2 +
           c1092sps_relSin x z / c1092sps_relCos x z) +
        c1092sps_wallWeight z / &2)`,
  REWRITE_TAC[c1092sps_leftPlus; c1092sps_scalarB; real_div] THEN REAL_ARITH_TAC);;

(* Lean: left_minus_affine *)
let C1092SPS_LEFT_MINUS_AFFINE = prove
 (`forall a x z. c1092sps_leftMinus a x z =
     c1092sps_leftMinus (&1) x z + (a - &1) *
       (c1092sps_cosH z / c1092sps_sinH x *
          (&3 / &2 + (c1092sps_cosH x * (c1092sps_cosH x + c1092sps_sinH x)) / &2 -
           c1092sps_relSin x z / c1092sps_relCos x z) +
        c1092sps_wallWeight z / &2)`,
  REWRITE_TAC[c1092sps_leftMinus; c1092sps_scalarB; real_div] THEN REAL_ARITH_TAC);;

(* Lean: wall_weight_pos *)
let C1092SPS_WALL_WEIGHT_POS = prove
 (`forall z. &0 <= z /\ z < &1 ==> &0 < c1092sps_wallWeight z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_COS_POS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= c1092sps_sinH z` ASSUME_TAC THENL
  [REWRITE_TAC[c1092sps_sinH] THEN MATCH_MP_TAC REAL_LE_DIV THEN
   MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092sps_wallWeight] THEN C1092SPS_POS_TAC);;

(* Lean: left_plus_pos *)
let C1092SPS_LEFT_PLUS_POS = prove
 (`forall a x z. &1 <= a /\ &0 < x /\ x <= &1 / &4 /\ x <= z /\ z < &1
           ==> &0 < c1092sps_leftPlus a x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SPS_WALL_DEN_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:real`; `z - x`] C1092SPSP_ASCENDINGP_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < c1092sps_leftPlus (&1) x z` ASSUME_TAC THENL
  [ASM_SIMP_TAC[C1092SPS_LEFT_PLUS_ONE] THEN
   SUBGOAL_THEN `&0 < &1 - z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C1092SPS_POS_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_COS_POS) THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_SIN_POS) THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_COS_POS) THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SPS_RELATIVE_COS_POS) THEN
  MP_TAC(SPEC `z:real` C1092SPS_WALL_WEIGHT_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092sps_relSin x z` ASSUME_TAC THENL
  [REWRITE_TAC[C1092SPS_RELATIVE_SIN_FACTOR] THEN
   SUBGOAL_THEN `&0 <= z - x /\ &0 <= &1 + x * z /\
                 &0 < &1 + x pow 2 /\ &0 < &1 + z pow 2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[C1092SPS_HALF_DEN_POS] THEN
    SUBGOAL_THEN `&0 <= x * z` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   C1092SPS_POS_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[C1092SPS_LEFT_PLUS_AFFINE] THEN
  MATCH_MP_TAC REAL_LTE_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  C1092SPS_POS_TAC);;

(* Lean: left_minus_pos *)
let C1092SPS_LEFT_MINUS_POS = prove
 (`forall a x z. &1 <= a /\ &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z <= x
           ==> &0 < c1092sps_leftMinus a x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `z < &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SPS_WALL_DEN_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`z:real`; `x - z`] C1092SPSP_DESCENDINGP_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < c1092sps_leftMinus (&1) x z` ASSUME_TAC THENL
  [ASM_SIMP_TAC[C1092SPS_LEFT_MINUS_ONE] THEN
   SUBGOAL_THEN `&0 < &1 - z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C1092SPS_POS_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_COS_POS) THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_SIN_POS) THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_COS_POS) THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SPS_RELATIVE_COS_POS) THEN
  MP_TAC(SPEC `z:real` C1092SPS_WALL_WEIGHT_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= --(c1092sps_relSin x z / c1092sps_relCos x z)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM C1092SPS_DIV_LNEG] THEN
   MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
   REWRITE_TAC[C1092SPS_RELATIVE_SIN_FACTOR; GSYM C1092SPS_DIV_LNEG] THEN
   SUBGOAL_THEN `&0 <= x - z /\ &0 <= &1 + x * z` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= x * z` MP_TAC THENL
    [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
   MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
   MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN REPEAT DISCH_TAC THEN
   MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `&0 <= &2 * (x - z) * w ==> &0 <= --(&2 * (z - x) * w)`) THEN
    C1092SPS_POS_TAC;
    C1092SPS_POS_TAC]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[C1092SPS_LEFT_MINUS_AFFINE] THEN
  MATCH_MP_TAC REAL_LTE_ADD THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[real_sub] THEN C1092SPS_POS_TAC);;

(* Lean: bottom_slope_factor *)
let C1092SPS_BOTTOM_SLOPE_FACTOR = prove
 (`forall x z. &0 < x
         ==> c1092sps_bottomSlope x z =
             ((x * z + x + z - &1) * c1092spsp_bottomQ x z) /
             (&2 * x * (&1 + x pow 2) * (&1 + z pow 2) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  REWRITE_TAC[c1092sps_bottomSlope; c1092sps_wallWeight; c1092sps_cosH; c1092sps_sinH;
              c1092spsp_bottomQ] THEN
  C1092SPS_FIELD_TAC);;

(* Lean: bottom_side_endpoint *)
let C1092SPS_BOTTOM_SIDE_ENDPOINT = prove
 (`forall x z. &0 < x
         ==> c1092sps_bottomMinus (c1092sps_cosH x + (&11 / &25) * c1092sps_sinH x) x z =
             (--(x * z + x + z - &1) * c1092spsp_bottomP x z) /
             (&25 * (&1 + x pow 2) pow 2 * (&1 + z pow 2) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  REWRITE_TAC[c1092sps_bottomMinus; c1092sps_wallWeight; c1092sps_cosH; c1092sps_sinH;
              c1092spsp_bottomP; c1092spsp_bottomB0; c1092spsp_bottomB1;
              c1092spsp_bottomB2; c1092spsp_bottomB3] THEN
  C1092SPS_FIELD_TAC);;

(* Lean: bottom_affine *)
let C1092SPS_BOTTOM_AFFINE = prove
 (`forall a b x z. c1092sps_bottomMinus a x z =
             c1092sps_bottomMinus b x z + (a - b) * c1092sps_bottomSlope x z`,
  REWRITE_TAC[c1092sps_bottomMinus; c1092sps_bottomSlope; real_div] THEN
  REAL_ARITH_TAC);;

(* Lean: bottom_minus_initial_pos *)
let C1092SPS_BOTTOM_MINUS_INITIAL_POS = prove
 (`forall a x z. &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z <= &5 / &12 /\
           a <= c1092sps_cosH x + (&11 / &25) * c1092sps_sinH x
           ==> &0 < c1092sps_bottomMinus a x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `x * z + x + z - &1 < &0` ASSUME_TAC THENL
  [SUBGOAL_THEN `x * z <= &1 / &4 * &1 / &2` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
   ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SPSP_BOTTOMQ_LOWER) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SPSP_BOTTOMP_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c1092sps_bottomSlope x z < &0` ASSUME_TAC THENL
  [ASM_SIMP_TAC[C1092SPS_BOTTOM_SLOPE_FACTOR] THEN
   REWRITE_TAC[REAL_ARITH `t < &0 <=> &0 < --t`; GSYM C1092SPS_DIV_LNEG;
               GSYM REAL_MUL_LNEG] THEN
   SUBGOAL_THEN `&0 < --(x * z + x + z - &1) /\ &0 < c1092spsp_bottomQ x z`
   STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C1092SPS_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c1092sps_bottomMinus
                  (c1092sps_cosH x + (&11 / &25) * c1092sps_sinH x) x z` ASSUME_TAC THENL
  [ASM_SIMP_TAC[C1092SPS_BOTTOM_SIDE_ENDPOINT] THEN
   SUBGOAL_THEN `&0 < --(x * z + x + z - &1)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   C1092SPS_POS_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[SPECL [`a:real`; `c1092sps_cosH x + (&11 / &25) * c1092sps_sinH x`]
    C1092SPS_BOTTOM_AFFINE] THEN
  MATCH_MP_TAC REAL_LTE_ADD THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: bottom_far_endpoint_identity *)
let C1092SPS_BOTTOM_FAR_ENDPOINT_IDENTITY = prove
 (`forall x. c1092sps_cosH x + c1092sps_sinH x - &1 - c1092sps_cosH x * c1092sps_sinH x +
       c1092sps_sinH x pow 2 / &2 =
       (&2 * x pow 3 * (&2 - x)) / (&1 + x pow 2) pow 2`,
  GEN_TAC THEN REWRITE_TAC[c1092sps_cosH; c1092sps_sinH] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_NZ) THEN CONV_TAC REAL_FIELD);;

(* Lean: bottom_far_endpoint_pos *)
let C1092SPS_BOTTOM_FAR_ENDPOINT_POS = prove
 (`forall x. &0 < x /\ x <= &1 / &4
       ==> &0 < c1092sps_cosH x + c1092sps_sinH x - &1 -
                c1092sps_cosH x * c1092sps_sinH x + c1092sps_sinH x pow 2 / &2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[C1092SPS_BOTTOM_FAR_ENDPOINT_IDENTITY] THEN
  SUBGOAL_THEN `&0 < &2 - x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN DISCH_TAC THEN
  C1092SPS_POS_TAC);;

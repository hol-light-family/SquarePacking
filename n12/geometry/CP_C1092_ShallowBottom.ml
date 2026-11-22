(* ========================================================================= *)
(* Port of Compact/Completion/C1092/ShallowBottom.lean                        *)
(* (N12Compact.C1092ShallowBottom).  Complete bottom-envelope scalar         *)
(* intervals on 0 <= z <= 1.  C1092ShallowPositiveScalars: C1092SPS_*,       *)
(* c1092sps_*; polynomials: c1092spsp_*; cubic_taylor_nonneg:                *)
(* C1092WP_CUBIC_TAYLOR_NONNEG.                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C1092ShallowPositiveScalars.ml";;
needs "n12/geometry/C1092WallPolynomial.ml";;
needs "n12/geometry/PositiveCentralTransverse.ml";;

let C1092SB_POWS_TAC x =
  MAP_EVERY (fun n -> MP_TAC(SPECL [x; mk_small_numeral n] REAL_POW_LE))
    [2;3;4;5] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC;;

(* Lean: bottomQ_full *)
let C1092SB_BOTTOMQ_FULL = prove
 (`forall x z. &0 <= x /\ x <= &1 / &4 /\ &0 <= z /\ z <= &1
         ==> &11 / &32 <= c1092spsp_bottomQ x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092SB_POWS_TAC `x:real` THEN C1092SB_POWS_TAC `z:real` THEN
  SUBGOAL_THEN `z pow 2 <= &1 /\ x pow 2 <= &1 / &16 /\ x pow 3 <= &1 / &64`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [C1092SPSP_POW_TAC `&1`; C1092SPSP_POW_TAC `&1 / &4`; C1092SPSP_POW_TAC `&1 / &4`];
   ALL_TAC] THEN
  SUBGOAL_THEN `z pow 3 <= &1` ASSUME_TAC THENL [C1092SPSP_POW_TAC `&1`; ALL_TAC] THEN
  PCT_PROD_TAC `&1 / &4 - x` `&1 + z + &5 * z pow 2 + z pow 3` THEN
  PCT_PROD_TAC `x pow 2` `z pow 3 - z pow 2 + &5 * z + &1` THEN
  PCT_PROD_TAC `x pow 3` `z pow 3 - z pow 2 + z + &1` THEN
  REWRITE_TAC[c1092spsp_bottomQ] THEN RASM_ARITH_TAC);;

(* Lean: bottomP_full *)
let C1092SB_BOTTOMP_FULL = prove
 (`forall x z. &0 <= x /\ x <= &1 / &4 /\ &0 <= z /\ z <= &1
         ==> &0 < c1092spsp_bottomP x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092SB_POWS_TAC `x:real` THEN C1092SB_POWS_TAC `z:real` THEN
  MP_TAC(SPECL [`&14 / &5`; `-- &22`; `&53`; `-- &22`; `&1 / &4`; `z:real`]
    C1092WP_CUBIC_TAYLOR_NONNEG) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `z pow 2 <= &1 /\ z pow 3 <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN C1092SPSP_POW_TAC `&1`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c1092spsp_bottomB0 z /\ &0 <= c1092spsp_bottomB1 z /\
                &0 <= &4 * c1092spsp_bottomB1 z + c1092spsp_bottomB2 z /\
                &0 <= c1092spsp_bottomB3 z` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[c1092spsp_bottomB0; c1092spsp_bottomB1; c1092spsp_bottomB2;
               c1092spsp_bottomB3] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  PCT_PROD_TAC `x:real` `&1 - &4 * x` THEN
  PCT_PROD_TAC `x * (&1 - &4 * x)` `c1092spsp_bottomB1 z` THEN
  PCT_PROD_TAC `x pow 2` `&4 * c1092spsp_bottomB1 z + c1092spsp_bottomB2 z` THEN
  PCT_PROD_TAC `x pow 3` `c1092spsp_bottomB3 z` THEN
  REWRITE_TAC[c1092spsp_bottomP] THEN RASM_ARITH_TAC);;

(* Lean: lower_nonneg *)
let C1092SB_LOWER_NONNEG = prove
 (`forall a x z. &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z <= &1 /\
           a <= c1092sps_cosH x + (&11 / &25) * c1092sps_sinH x /\
           x * z + x + z <= &1
           ==> &0 <= c1092sps_bottomMinus a x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SB_BOTTOMP_FULL) THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SB_BOTTOMQ_FULL) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `c1092sps_bottomSlope x z <= &0` ASSUME_TAC THENL
  [ASM_SIMP_TAC[C1092SPS_BOTTOM_SLOPE_FACTOR] THEN
   REWRITE_TAC[REAL_ARITH `t <= &0 <=> &0 <= --t`; GSYM C1092SPS_DIV_LNEG;
               GSYM REAL_MUL_LNEG] THEN
   SUBGOAL_THEN `&0 <= --(x * z + x + z - &1) /\ &0 <= c1092spsp_bottomQ x z`
   STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   C1092SPS_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c1092sps_bottomMinus
                  (c1092sps_cosH x + (&11 / &25) * c1092sps_sinH x) x z` ASSUME_TAC THENL
  [ASM_SIMP_TAC[C1092SPS_BOTTOM_SIDE_ENDPOINT] THEN
   SUBGOAL_THEN `&0 <= --(x * z + x + z - &1)` ASSUME_TAC THENL
   [RASM_ARITH_TAC; ALL_TAC] THEN C1092SPS_POS_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[SPECL [`a:real`; `c1092sps_cosH x + (&11 / &25) * c1092sps_sinH x`]
    C1092SPS_BOTTOM_AFFINE] THEN
  MATCH_MP_TAC REAL_LE_ADD THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[GSYM REAL_NEG_MUL2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
  RASM_ARITH_TAC);;

(* Lean: upperBase, upperWeight (definitions) *)
let c1092sb_upperBase = new_definition
 `c1092sb_upperBase (x:real) (z:real) =
    z * (&1 - z) pow 2 + x * z * (&1 - z pow 2) +
    x pow 2 * (&1 + &4 * z - z pow 2 + &4 * z pow 3) +
    x pow 3 * (&1 - &2 * z + z pow 2 - &4 * z pow 3) +
    &2 * x pow 4 * (-- &1 + z - z pow 2 + z pow 3)`;;
let c1092sb_upperWeight = new_definition
 `c1092sb_upperWeight (x:real) (z:real) =
    (&1 + z + z pow 2 + z pow 3) + x * (&2 + z + z pow 3) +
    x pow 2 * (&2 + z + &2 * z pow 2 - z pow 3) +
    x pow 3 * (&1 + &2 * z - z pow 2 + &2 * z pow 3) +
    x pow 4 * (&1 + z pow 2 - &2 * z pow 3) +
    x pow 5 * (-- &1 + z - z pow 2 + z pow 3)`;;

(* Lean: upper_polynomials *)
let C1092SB_UPPER_POLYNOMIALS = prove
 (`forall x z. &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z <= &1
         ==> &0 < c1092sb_upperBase x z /\ &0 < c1092sb_upperWeight x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  C1092SB_POWS_TAC `x:real` THEN C1092SB_POWS_TAC `z:real` THEN
  SUBGOAL_THEN `z pow 2 <= &1 /\ x pow 2 <= &1 / &16 /\ x pow 5 <= &1 / &1024`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [C1092SPSP_POW_TAC `&1`; C1092SPSP_POW_TAC `&1 / &4`; C1092SPSP_POW_TAC `&1 / &4`];
   ALL_TAC] THEN
  PCT_PROD_TAC `z pow 2` `&1 - z` THEN
  SUBGOAL_THEN `z pow 3 <= z pow 2` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `&1 - z` REAL_LE_POW_2) THEN DISCH_TAC THEN
  PCT_PROD_TAC `z:real` `(&1 - z) pow 2` THEN
  PCT_PROD_TAC `x:real` `z:real` THEN PCT_PROD_TAC `x * z` `&1 - z pow 2` THEN
  PCT_PROD_TAC `z pow 3` `&1 - x` THEN
  PCT_PROD_TAC `x:real` `(&1 - z) pow 2` THEN
  PCT_PROD_TAC `x pow 2` `&2 - (&1 - z) * (&1 + z pow 2)` THEN
  PCT_PROD_TAC `z:real` `&4 - z` THEN
  SUBGOAL_THEN `&0 < &1 + &4 * z - z pow 2 + &4 * z pow 3 +
                    x * (&1 - &2 * z + z pow 2 - &4 * z pow 3) +
                    &2 * x pow 2 * (-- &1 + z - z pow 2 + z pow 3)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  PCT_PRODLT_TAC `x:real` `x:real` THEN
  PCT_PRODLT_TAC `x * x`
    `&1 + &4 * z - z pow 2 + &4 * z pow 3 + x * (&1 - &2 * z + z pow 2 - &4 * z pow 3) +
     &2 * x pow 2 * (-- &1 + z - z pow 2 + z pow 3)` THEN
  PCT_PROD_TAC `x:real` `&2 + z + z pow 3` THEN
  PCT_PROD_TAC `x pow 2` `&2 + z + &2 * z pow 2 - z pow 3` THEN
  PCT_PROD_TAC `x pow 3` `&1 + &2 * z - z pow 2 + &2 * z pow 3` THEN
  PCT_PROD_TAC `x pow 4` `&1 + z pow 2 - &2 * z pow 3` THEN
  PCT_PROD_TAC `x pow 5` `&1 + z - z pow 2 + z pow 3` THEN
  REWRITE_TAC[c1092sb_upperBase; c1092sb_upperWeight] THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: upper (definition) *)
let c1092sb_upper = new_definition
 `c1092sb_upper (a:real) (x:real) (z:real) =
    --c1092sps_cosH z *
      ((c1092sps_scalarB a x - c1092sps_sinH x - &2 * c1092sps_cosH x) / c1092sps_sinH x) -
    &2 * c1092sps_sinH z + (a * c1092sps_wallWeight z) / &2 -
    ((c1092sps_sinH x * c1092sps_sinH z - c1092sps_cosH x * c1092sps_cosH z) *
       (--c1092sps_sinH x / &2) +
     (c1092sps_sinH x * c1092sps_cosH z + c1092sps_cosH x * c1092sps_sinH z) *
       (c1092sps_sinH x - a) -
     a * (c1092sps_sinH x * c1092sps_sinH z - c1092sps_cosH x * c1092sps_cosH z))`;;

(* Lean: upper_factor *)
let C1092SB_UPPER_FACTOR = prove
 (`forall a x z. &0 < x
     ==> c1092sb_upper a x z =
         ((x * z + x + z - &1) * c1092sb_upperBase x z) /
           ((&1 + x pow 2) pow 2 * (&1 + z pow 2) pow 2) +
         ((a - &1) * (x * z + x + z - &1) * c1092sb_upperWeight x z) /
           (x * (&1 + x pow 2) pow 2 * (&1 + z pow 2) pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(x = &0)` MP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN DISCH_TAC THEN
  REWRITE_TAC[c1092sb_upper; c1092sb_upperBase; c1092sb_upperWeight;
              c1092sps_scalarB; c1092sps_wallWeight; c1092sps_cosH; c1092sps_sinH] THEN
  C1092SPS_FIELD_TAC);;

(* Lean: upper_nonneg *)
let C1092SB_UPPER_NONNEG = prove
 (`forall a x z. &1 <= a /\ &0 < x /\ x <= &1 / &4 /\ &0 <= z /\ z <= &1 /\
           &1 <= x * z + x + z
           ==> &0 <= c1092sb_upper a x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`x:real`; `z:real`] C1092SB_UPPER_POLYNOMIALS) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[C1092SB_UPPER_FACTOR] THEN
  MP_TAC(SPEC `x:real` C1092SPS_HALF_DEN_POS) THEN
  MP_TAC(SPEC `z:real` C1092SPS_HALF_DEN_POS) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= x * z + x + z - &1 /\ &0 <= a - &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C1092SPS_POS_TAC);;

(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperGapPolynomials.lean (Jatloe, N12-jatloe;  *)
(* namespace N12Compact.C868.UpperGapScalars).  Small exact algebra for the  *)
(* two C868 upper-sector margins.  Normal: c977cc_normal; normal_bounds:     *)
(* C977CC_NORMAL_BOUNDS; C1092WallProfileScalars.half / quarter_data:        *)
(* C1092WPS_half / C1092WPS_QUARTER_DATA.                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: firstPolynomial *)
let C868GP_firstPolynomial = new_definition
 `C868GP_firstPolynomial (x:real) =
    -- &25 + &23700 * x - &10324 * x pow 2 - &29100 * x pow 3 - &100598 * x pow 4 -
    &129300 * x pow 5 - &170324 * x pow 6 - &76500 * x pow 7 - &80025 * x pow 8`;;

(* Lean: secondPolynomial *)
let C868GP_secondPolynomial = new_definition
 `C868GP_secondPolynomial (x:real) =
    -- &289 + &8200 * x - &23596 * x pow 2 + &45400 * x pow 3 - &73214 * x pow 4 +
    &66200 * x pow 5 - &76796 * x pow 6 + &29000 * x pow 7 - &26889 * x pow 8`;;

(* Lean: first_polynomial *)
let C868GP_FIRST_POLYNOMIAL = prove
 (`forall x. &1 / &8 <= x /\ x <= &5 / &12 ==> &0 <= C868GP_firstPolynomial x`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY (fun n ->
    MP_TAC(SPECL [mk_small_numeral n; `x:real`; `&5 / &12`] REAL_POW_LE2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONV_RULE(RAND_CONV REAL_RAT_REDUCE_CONV)))
    [2;3;4;5;6;7] THEN
  SUBGOAL_THEN
   `&400 <= &23700 - &10324 * x - &29100 * x pow 2 - &100598 * x pow 3 -
            &129300 * x pow 4 - &170324 * x pow 5 - &76500 * x pow 6 -
            &80025 * x pow 7` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= x * ((&23700 - &10324 * x - &29100 * x pow 2 - &100598 * x pow 3 -
            &129300 * x pow 4 - &170324 * x pow 5 - &76500 * x pow 6 -
            &80025 * x pow 7) - &400)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&1 / &8 <= x` THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  REWRITE_TAC[C868GP_firstPolynomial] THEN REAL_ARITH_TAC);;

(* Lean: second_polynomial *)
let C868GP_SECOND_POLYNOMIAL = prove
 (`forall x. &1 / &8 <= x /\ x <= &5 / &12 ==> &0 <= C868GP_secondPolynomial x`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= ((x - &1 / &8) * (&5 / &12 - x)) *
          (&23600 - &14800 * (x + &1 / &8 + &5 / &12))` ASSUME_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= -- &289 + &8200 * x - &23600 * x pow 2 + &14800 * x pow 3`
  ASSUME_TAC THENL
  [UNDISCH_TAC `&1 / &8 <= x` THEN UNDISCH_TAC `x <= &5 / &12` THEN
   UNDISCH_TAC
    `&0 <= ((x - &1 / &8) * (&5 / &12 - x)) *
           (&23600 - &14800 * (x + &1 / &8 + &5 / &12))` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= x pow 3 * (&30600 - &73214 * x) /\
    &0 <= x pow 5 * (&66200 - &76796 * x) /\
    &0 <= x pow 7 * (&29000 - &26889 * x)` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_SIMP_TAC[REAL_POW_LE] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
  REWRITE_TAC[C868GP_secondPolynomial] THEN REAL_ARITH_TAC);;

(* x = half c s with its rational parametrisation *)
let C868GP_HALF_TAC =
  FIRST_ASSUM(fun th ->
    let th' = check (fun th -> fst(strip_comb(concl th)) = `c977cc_normal`) th in
    let c,s = match snd(strip_comb(concl th')) with [c;s] -> c,s | _ -> fail() in
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th') THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th') THEN
    MP_TAC(SPECL [c; s] C1092WPS_QUARTER_DATA) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC (mk_eq(`x:real`, list_mk_comb(`C1092WPS_half`,[c; s]))) THEN
    STRIP_TAC);;

(* Lean: half_upper *)
let C868GP_HALF_UPPER = prove
 (`forall c s. c977cc_normal c s
         ==> &0 <= C1092WPS_half c s /\ C1092WPS_half c s <= &5 / &12`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C868GP_HALF_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (&1 + x pow 2) * (c - s)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN
   MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &1 - &2 * x - x pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `&0 <= (&1 + x pow 2) * (c - s)` THEN
   UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
   UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (x - &5 / &12) * (x + &5 / &12 + &2)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&0 <= &1 - &2 * x - x pow 2` THEN REAL_ARITH_TAC);;

(* Lean: half_lower_of_tilt *)
let C868GP_HALF_LOWER_OF_TILT = prove
 (`forall c s. c977cc_normal c s /\ &9 * c <= &35 * s
         ==> &1 / &8 <= C1092WPS_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C868GP_HALF_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= (&1 + x pow 2) * (&35 * s - &9 * c)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN
   MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&9 <= &70 * x + &9 * x pow 2` ASSUME_TAC THENL
  [UNDISCH_TAC `&0 <= (&1 + x pow 2) * (&35 * s - &9 * c)` THEN
   UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
   UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `x * x <= x * (&1 / &8)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `&9 <= &70 * x + &9 * x pow 2` THEN
  UNDISCH_TAC `x < &1 / &8` THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

(* Lean: disk_margin *)
let C868GP_DISK_MARGIN = prove
 (`forall A B C t. C pow 2 + t pow 2 = &1 /\ A pow 2 + B pow 2 <= &1
             ==> &0 <= &1 + C * A + t * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(C * A + t * B) pow 2 <= &1` MP_TAC THENL
  [SUBGOAL_THEN `(C * A + t * B) pow 2 + (t * A - C * B) pow 2 =
                 (A pow 2 + B pow 2) * (C pow 2 + t pow 2)` MP_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REWRITE_TAC[REAL_MUL_RID] THEN
   MP_TAC(SPEC `t * A - C * B` REAL_LE_POW_2) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`C * A + t * B`,`y:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  NLIN_TAC []);;

(* Lean: circle_arc *)
let C868GP_CIRCLE_ARC = prove
 (`forall c s. c977cc_normal c s ==> &1 + (&4 / &5) * c * s <= c + s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  UNDISCH_TAC `c977cc_normal c s` THEN
  REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (c + s - &1) * (&10 / &7 - (c + s))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= c * s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

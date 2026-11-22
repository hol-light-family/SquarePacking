(* ========================================================================= *)
(* Port of Compact/Geometry/C1092ShallowPositiveScalarsPolynomials.lean       *)
(* (Jatloe, N12-jatloe).  Polynomial inequalities of the continuous          *)
(* shallow-positive C1092 wall argument, by coefficient estimates.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;

(* a structural positivity tactic (Lean: positivity) for goals &0 <= p,     *)
(* &0 < p built from +, *, pow, numerals and assumptions &0 <= x, &0 < x.   *)
let rec C1092SPSP_POS_TAC g =
  (FIRST
    [CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
     FIRST_ASSUM ACCEPT_TAC;
     FIRST_ASSUM(fun th -> ACCEPT_TAC(MATCH_MP REAL_LT_IMP_LE th));
     MATCH_ACCEPT_TAC REAL_LE_POW_2;
     MATCH_ACCEPT_TAC REAL_LE_SQUARE;
     MATCH_MP_TAC REAL_LT_ADD THEN CONJ_TAC THEN C1092SPSP_POS_TAC;
     MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THEN C1092SPSP_POS_TAC;
     MATCH_MP_TAC REAL_LET_ADD THEN CONJ_TAC THEN C1092SPSP_POS_TAC;
     MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN C1092SPSP_POS_TAC;
     MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C1092SPSP_POS_TAC;
     MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C1092SPSP_POS_TAC;
     MATCH_MP_TAC REAL_POW_LT THEN C1092SPSP_POS_TAC;
     MATCH_MP_TAC REAL_POW_LE THEN C1092SPSP_POS_TAC]) g;;

(* Lean: power_le_bound *)
let C1092SPSP_POWER_LE_BOUND = prove
 (`forall z b n. &0 <= z /\ z <= b ==> z pow n <= b pow n`,
  MESON_TAC[REAL_POW_LE2]);;

(* numeric instance: z pow n <= c from &0 <= z, z <= b, b pow n = c *)
let C1092SPSP_POW_BOUND = prove
 (`forall z b n c. &0 <= z /\ z <= b /\ b pow n = c ==> z pow n <= c`,
  MESON_TAC[REAL_POW_LE2]);;

let C1092SPSP_POW_TAC b =
  MATCH_MP_TAC C1092SPSP_POW_BOUND THEN EXISTS_TAC b THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;;

(* Lean: bottomQ (definition) *)
let c1092spsp_bottomQ = new_definition
 `c1092spsp_bottomQ (x:real) (z:real) =
    (&1 + z + z pow 2 + z pow 3) - x * (&1 + z + &5 * z pow 2 + z pow 3) +
    x pow 2 * (z pow 3 - z pow 2 + &5 * z - &1) +
    x pow 3 * (z pow 3 - z pow 2 + z - &1)`;;

(* Lean: bottomB0 .. bottomB3, bottomP (definitions) *)
let c1092spsp_bottomB0 = new_definition
 `c1092spsp_bottomB0 (z:real) = &3 - &22 * z + &53 * z pow 2 - &22 * z pow 3`;;
let c1092spsp_bottomB1 = new_definition
 `c1092spsp_bottomB1 (z:real) = &50 - &3 * z + &94 * z pow 2 + &47 * z pow 3`;;
let c1092spsp_bottomB2 = new_definition
 `c1092spsp_bottomB2 (z:real) = &47 - &94 * z - &3 * z pow 2 - &50 * z pow 3`;;
let c1092spsp_bottomB3 = new_definition
 `c1092spsp_bottomB3 (z:real) = &22 + &53 * z + &22 * z pow 2 + &3 * z pow 3`;;
let c1092spsp_bottomP = new_definition
 `c1092spsp_bottomP (x:real) (z:real) =
    c1092spsp_bottomB0 z + x * c1092spsp_bottomB1 z +
    x pow 2 * c1092spsp_bottomB2 z + x pow 3 * c1092spsp_bottomB3 z`;;

(* Lean: bottomQ_lower *)
let C1092SPSP_BOTTOMQ_LOWER = prove
 (`forall x z. &0 <= x /\ x <= &1 / &4 /\ &0 <= z /\ z <= &1 / &2
         ==> &47 / &256 <= c1092spsp_bottomQ x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `z pow 2 <= &1 / &4 /\ z pow 3 <= &1 / &8 /\
                x pow 2 <= &1 / &16 /\ x pow 3 <= &1 / &64`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [C1092SPSP_POW_TAC `&1 / &2`; C1092SPSP_POW_TAC `&1 / &2`;
    C1092SPSP_POW_TAC `&1 / &4`; C1092SPSP_POW_TAC `&1 / &4`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z pow 2 /\ &0 <= z pow 3 /\ &0 <= x pow 2 /\ &0 <= x pow 3`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN C1092SPSP_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 + z + &5 * z pow 2 + z pow 3 <= &23 / &8 /\
                &0 <= &1 + z + &5 * z pow 2 + z pow 3 /\
                --(&5 / &4) <= z pow 3 - z pow 2 + &5 * z - &1 /\
                --(&5 / &4) <= z pow 3 - z pow 2 + z - &1`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `x * (&1 + z + &5 * z pow 2 + z pow 3) <= &1 / &4 * &23 / &8 /\
    &0 <= x pow 2 * ((z pow 3 - z pow 2 + &5 * z - &1) - --(&5 / &4)) /\
    &0 <= x pow 3 * ((z pow 3 - z pow 2 + z - &1) - --(&5 / &4))`
  MP_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[c1092spsp_bottomQ] THEN
  UNDISCH_TAC `x pow 2 <= &1 / &16` THEN UNDISCH_TAC `x pow 3 <= &1 / &64` THEN
  UNDISCH_TAC `&0 <= z` THEN UNDISCH_TAC `&0 <= z pow 2` THEN
  UNDISCH_TAC `&0 <= z pow 3` THEN
  REAL_ARITH_TAC);;

(* Lean: bottom_coefficients *)
let C1092SPSP_BOTTOM_COEFFICIENTS = prove
 (`forall z. &0 <= z /\ z <= &5 / &12
       ==> &63 / &263 <= c1092spsp_bottomB0 z /\ &195 / &4 <= c1092spsp_bottomB1 z /\
           &3193 / &864 <= c1092spsp_bottomB2 z /\ &22 <= c1092spsp_bottomB3 z`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `z pow 2 <= &25 / &144 /\ z pow 3 <= &125 / &1728`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN C1092SPSP_POW_TAC `&5 / &12`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z pow 2 /\ &0 <= z pow 3` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN C1092SPSP_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z pow 2 * (&55 / &6 - &22 * z)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `z - &66 / &263` REAL_LE_POW_2) THEN DISCH_TAC THEN
  REWRITE_TAC[c1092spsp_bottomB0; c1092spsp_bottomB1; c1092spsp_bottomB2;
              c1092spsp_bottomB3] THEN
  REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: bottomP_pos *)
let C1092SPSP_BOTTOMP_POS = prove
 (`forall x z. &0 <= x /\ &0 <= z /\ z <= &5 / &12 ==> &0 < c1092spsp_bottomP x z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:real` C1092SPSP_BOTTOM_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= x * c1092spsp_bottomB1 z /\
                &0 <= x pow 2 * c1092spsp_bottomB2 z /\
                &0 <= x pow 3 * c1092spsp_bottomB3 z` MP_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092spsp_bottomP] THEN ASM_REAL_ARITH_TAC);;

(* Lean: ascendingC0 .. ascendingC5, ascendingP (definitions) *)
let c1092spsp_ascC0 = new_definition
 `c1092spsp_ascC0 (x:real) = &2 * x pow 2 * (&1 + x pow 2) pow 4`;;
let c1092spsp_ascC1 = new_definition
 `c1092spsp_ascC1 (x:real) =
    &2 * x * (&1 + x pow 2) pow 2 * (&5 * x pow 4 + &7 * x pow 2 + &4)`;;
let c1092spsp_ascC2 = new_definition
 `c1092spsp_ascC2 (x:real) =
    (&1 + x pow 2) * (&20 * x pow 6 + &34 * x pow 4 + x pow 3 + &25 * x pow 2 + x + &3)`;;
let c1092spsp_ascC3 = new_definition
 `c1092spsp_ascC3 (x:real) =
    &20 * x pow 7 + &38 * x pow 5 + &5 * x pow 4 + &32 * x pow 3 + &6 * x pow 2 +
    &6 * x + &1`;;
let c1092spsp_ascC4 = new_definition
 `c1092spsp_ascC4 (x:real) =
    &10 * x pow 6 + &10 * x pow 4 + &7 * x pow 3 + &7 * x pow 2 + &3 * x - &1`;;
let c1092spsp_ascC5 = new_definition
 `c1092spsp_ascC5 (x:real) = &2 * x pow 5 + &3 * x pow 2 + &1`;;
let c1092spsp_ascP = new_definition
 `c1092spsp_ascP (x:real) (rho:real) =
    c1092spsp_ascC0 x + c1092spsp_ascC1 x * rho + c1092spsp_ascC2 x * rho pow 2 +
    c1092spsp_ascC3 x * rho pow 3 + c1092spsp_ascC4 x * rho pow 4 +
    c1092spsp_ascC5 x * rho pow 5`;;

(* Lean: ascending_coefficients *)
let C1092SPSP_ASCENDING_COEFFICIENTS = prove
 (`forall x. &0 < x
       ==> &0 < c1092spsp_ascC0 x /\ &0 <= c1092spsp_ascC1 x /\
           &0 <= c1092spsp_ascC2 x /\ &1 <= c1092spsp_ascC3 x /\
           --(&1) <= c1092spsp_ascC4 x /\ &0 <= c1092spsp_ascC5 x`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= x` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092spsp_ascC0; c1092spsp_ascC1; c1092spsp_ascC2; c1092spsp_ascC5] THEN
  REPEAT CONJ_TAC THEN TRY C1092SPSP_POS_TAC THENL
  [SUBGOAL_THEN `&0 <= &20 * x pow 7 + &38 * x pow 5 + &5 * x pow 4 +
                       &32 * x pow 3 + &6 * x pow 2 + &6 * x` MP_TAC THENL
   [C1092SPSP_POS_TAC; REWRITE_TAC[c1092spsp_ascC3] THEN REAL_ARITH_TAC];
   SUBGOAL_THEN `&0 <= &10 * x pow 6 + &10 * x pow 4 + &7 * x pow 3 +
                       &7 * x pow 2 + &3 * x` MP_TAC THENL
   [C1092SPSP_POS_TAC; REWRITE_TAC[c1092spsp_ascC4] THEN REAL_ARITH_TAC]]);;

(* Lean: ascendingP_pos *)
let C1092SPSP_ASCENDINGP_POS = prove
 (`forall x rho. &0 < x /\ &0 <= rho /\ rho <= &1 ==> &0 < c1092spsp_ascP x rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `x:real` C1092SPSP_ASCENDING_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rho pow 2 /\ &0 <= rho pow 3 /\ &0 <= rho pow 4 /\
                &0 <= rho pow 5` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN C1092SPSP_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= c1092spsp_ascC1 x * rho /\ &0 <= c1092spsp_ascC2 x * rho pow 2 /\
    &1 * rho pow 3 <= c1092spsp_ascC3 x * rho pow 3 /\
    --(&1) * rho pow 4 <= c1092spsp_ascC4 x * rho pow 4 /\
    &0 <= c1092spsp_ascC5 x * rho pow 5 /\
    &0 <= rho pow 3 * (&1 - rho)` MP_TAC THENL
  [REPEAT CONJ_TAC THEN
   (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_RMUL) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092spsp_ascP] THEN
  UNDISCH_TAC `&0 < c1092spsp_ascC0 x` THEN REAL_ARITH_TAC);;

(* Lean: descendingE0 .. descendingE6, descendingP (definitions) *)
let c1092spsp_descE0 = new_definition
 `c1092spsp_descE0 (z:real) = &2 * z pow 3 * (&1 + z pow 2) pow 4`;;
let c1092spsp_descE1 = new_definition
 `c1092spsp_descE1 (z:real) =
    (&1 + z pow 2) pow 2 *
    (&12 * z pow 6 + &3 * z pow 5 + &16 * z pow 4 + &3 * z pow 3 + z pow 2 + &1)`;;
let c1092spsp_descE2 = new_definition
 `c1092spsp_descE2 (z:real) =
    (&1 + z pow 2) *
    (&30 * z pow 7 + &15 * z pow 6 + &51 * z pow 5 + &21 * z pow 4 + &14 * z pow 3 +
     &5 * z pow 2 + z - &1)`;;
let c1092spsp_descE3 = new_definition
 `c1092spsp_descE3 (z:real) =
    &40 * z pow 8 + &30 * z pow 7 + &84 * z pow 6 + &55 * z pow 5 + &43 * z pow 4 +
    &26 * z pow 3 + &8 * z pow 2 + z + &1`;;
let c1092spsp_descE4 = new_definition
 `c1092spsp_descE4 (z:real) =
    &30 * z pow 7 + &30 * z pow 6 + &46 * z pow 5 + &39 * z pow 4 + &10 * z pow 3 +
    &8 * z pow 2 + &6 * z - &1`;;
let c1092spsp_descE5 = new_definition
 `c1092spsp_descE5 (z:real) =
    (&1 + z) * (&12 * z pow 5 + &3 * z pow 4 + &9 * z pow 3 + &3 * z pow 2 - &5 * z + &2)`;;
let c1092spsp_descE6 = new_definition
 `c1092spsp_descE6 (z:real) = (&1 + z) * (&1 + z pow 2) * (&2 * z pow 2 + z - &2)`;;
let c1092spsp_descP = new_definition
 `c1092spsp_descP (z:real) (rho:real) =
    c1092spsp_descE0 z + c1092spsp_descE1 z * rho + c1092spsp_descE2 z * rho pow 2 +
    c1092spsp_descE3 z * rho pow 3 + c1092spsp_descE4 z * rho pow 4 +
    c1092spsp_descE5 z * rho pow 5 + c1092spsp_descE6 z * rho pow 6`;;

(* Lean: descending_coefficients *)
let C1092SPSP_DESCENDING_COEFFICIENTS = prove
 (`forall z. &0 <= z /\ z <= &1 / &4
       ==> &0 <= c1092spsp_descE0 z /\ &1 <= c1092spsp_descE1 z /\
           --(&17 / &16) <= c1092spsp_descE2 z /\ &0 <= c1092spsp_descE3 z /\
           --(&1) <= c1092spsp_descE4 z /\ &0 < c1092spsp_descE5 z /\
           --(&85 / &32) <= c1092spsp_descE6 z`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `z pow 2 <= &1 / &16` ASSUME_TAC THENL
  [C1092SPSP_POW_TAC `&1 / &4`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= z pow 2` ASSUME_TAC THENL [C1092SPSP_POS_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC[c1092spsp_descE0] THEN C1092SPSP_POS_TAC;
   SUBGOAL_THEN `&1 <= (&1 + z pow 2) pow 2` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN
    SUBGOAL_THEN `&0 <= z pow 2 * z pow 2` MP_TAC THENL
    [C1092SPSP_POS_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&1 <= &12 * z pow 6 + &3 * z pow 5 + &16 * z pow 4 +
                       &3 * z pow 3 + z pow 2 + &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= &12 * z pow 6 + &3 * z pow 5 + &16 * z pow 4 +
                        &3 * z pow 3 + z pow 2` MP_TAC THENL
    [C1092SPSP_POS_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
   REWRITE_TAC[c1092spsp_descE1] THEN
   GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN
   MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
   SUBGOAL_THEN `&0 <= (&1 + z pow 2) *
                   (&30 * z pow 7 + &15 * z pow 6 + &51 * z pow 5 + &21 * z pow 4 +
                    &14 * z pow 3 + &5 * z pow 2 + z)` MP_TAC THENL
   [C1092SPSP_POS_TAC; ALL_TAC] THEN
   REWRITE_TAC[c1092spsp_descE2] THEN ASM_REAL_ARITH_TAC;
   REWRITE_TAC[c1092spsp_descE3] THEN C1092SPSP_POS_TAC;
   SUBGOAL_THEN `&0 <= &30 * z pow 7 + &30 * z pow 6 + &46 * z pow 5 +
                       &39 * z pow 4 + &10 * z pow 3 + &8 * z pow 2 + &6 * z` MP_TAC THENL
   [C1092SPSP_POS_TAC; REWRITE_TAC[c1092spsp_descE4] THEN REAL_ARITH_TAC];
   SUBGOAL_THEN `&0 <= &12 * z pow 5 + &3 * z pow 4 + &9 * z pow 3 + &3 * z pow 2`
   ASSUME_TAC THENL [C1092SPSP_POS_TAC; ALL_TAC] THEN
   REWRITE_TAC[c1092spsp_descE5] THEN MATCH_MP_TAC REAL_LT_MUL THEN
   ASM_REAL_ARITH_TAC;
   SUBGOAL_THEN `(&1 + z) * (&1 + z pow 2) <= &85 / &64` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&5 / &4 * &17 / &16` THEN
    CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC;
                    REAL_ARITH_TAC]; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (&1 + z) * (&1 + z pow 2) * (&2 * z pow 2 + z)` MP_TAC THENL
   [C1092SPSP_POS_TAC; ALL_TAC] THEN
   REWRITE_TAC[c1092spsp_descE6] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: descendingP_lower *)
let C1092SPSP_DESCENDINGP_LOWER = prove
 (`forall z rho. &0 <= z /\ z <= &1 / &4 /\ &0 <= rho /\ rho <= &1 / &4
           ==> c1092spsp_descE0 z + (&493 / &1024) * rho <= c1092spsp_descP z rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `z:real` C1092SPSP_DESCENDING_COEFFICIENTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= rho pow 2 /\ &0 <= rho pow 3 /\ &0 <= rho pow 4 /\
                &0 <= rho pow 5 /\ &0 <= rho pow 6` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN C1092SPSP_POS_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `rho pow 3 <= &1 / &64 /\ rho pow 5 <= &1 / &1024`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN C1092SPSP_POW_TAC `&1 / &4`; ALL_TAC] THEN
  SUBGOAL_THEN `&493 / &1024 <= &1 - &2 * rho - rho pow 3 - &3 * rho pow 5`
  ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&1 * rho <= c1092spsp_descE1 z * rho /\
    --(&2) * rho pow 2 <= c1092spsp_descE2 z * rho pow 2 /\
    &0 <= c1092spsp_descE3 z * rho pow 3 /\
    --(&1) * rho pow 4 <= c1092spsp_descE4 z * rho pow 4 /\
    &0 <= c1092spsp_descE5 z * rho pow 5 /\
    --(&3) * rho pow 6 <= c1092spsp_descE6 z * rho pow 6 /\
    rho * (&493 / &1024) <= rho * (&1 - &2 * rho - rho pow 3 - &3 * rho pow 5)`
  MP_TAC THENL
  [REPEAT CONJ_TAC THEN
   (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LE_RMUL ORELSE
    MATCH_MP_TAC REAL_LE_LMUL) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092spsp_descP] THEN
  REAL_ARITH_TAC);;

(* Lean: descendingP_pos *)
let C1092SPSP_DESCENDINGP_POS = prove
 (`forall z rho. &0 <= z /\ z <= &1 / &4 /\ &0 <= rho /\ rho <= &1 / &4 /\ &0 < z + rho
           ==> &0 < c1092spsp_descP z rho`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`z:real`; `rho:real`] C1092SPSP_DESCENDINGP_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `rho = &0` THENL
  [SUBGOAL_THEN `&0 < c1092spsp_descE0 z` MP_TAC THENL
   [SUBGOAL_THEN `&0 < z` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[c1092spsp_descE0] THEN C1092SPSP_POS_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   SUBGOAL_THEN `&0 <= c1092spsp_descE0 z` MP_TAC THENL
   [REWRITE_TAC[c1092spsp_descE0] THEN C1092SPSP_POS_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

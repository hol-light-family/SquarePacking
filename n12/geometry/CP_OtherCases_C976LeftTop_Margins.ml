(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976LeftTop/Margins.lean             *)
(* (N12Compact.Completion.OtherCases.C976LeftTop.Scalars).  The two          *)
(* one-angle inequalities f0, f1 of C976-LEFT-TOP-ANGLE section 5.           *)
(* Real.sqrt is HOL sqrt.                                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976LeftTop_Scalars.ml";;

let C976LTM_LIN = NLIN_TAC ~deg2:false [];;

let C976LTM_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C976LTM_LIN; ALL_TAC];;

let C976LTM_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C976LTM_LIN; ALL_TAC];;

let C976LTM_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

(* Lean: left_low_margin *)
let C976LTM_LEFT_LOW_MARGIN = prove
 (`forall l h. &0 < l /\ &0 < h /\ l pow 2 + h pow 2 = &1 /\ (&1 / &3) * l <= h /\ h <= l / &2
         ==> &0 < (&37 / &100) * l + (&11 / &100) * h - &189 / &625 -
                  (&169 / &5000) * l pow 2 - (&39 / &625) * l * h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  C976LTM_PROD `&0 <= (&3 * h - l) * (&3 * h + l)` THEN
  C976LTM_PROD `&0 <= (l - &2 * h) * (l + &2 * h)` THEN
  C976LTM_FACT `&4 / &5 <= l * l` THEN
  C976LTM_FACT `&1 / &10 <= h * h` THEN
  C976LTM_PROD `&0 <= (l - &2 * h) * (&2 * l - h)` THEN
  C976LTM_FACT `l * h <= &2 / &5` THEN
  SUBGOAL_THEN `&89 / &100 < l` ASSUME_TAC THENL
   [C976LTM_CONTRA THEN C976LTM_PROD `&0 <= (&89 / &100 - l) * (&89 / &100 + l)` THEN
    C976LTM_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `&31 / &100 < h` ASSUME_TAC THENL
   [C976LTM_CONTRA THEN C976LTM_PROD `&0 <= (&31 / &100 - h) * (&31 / &100 + h)` THEN
    C976LTM_LIN; ALL_TAC] THEN
  C976LTM_LIN);;

(* Lean: f1 (private definition) *)
let c976ltm_f1 = new_definition
 `c976ltm_f1 (l:real) (h:real) =
    (&37 / &100) * l + (&11 / &100) * h - &219 / &625 + (&17 / &625) * l pow 2 -
    (&161 / &2500) * l * h`;;

(* Lean: high_endpoint (private) *)
let C976LTM_HIGH_ENDPOINT = prove
 (`exists L H. &0 < L /\ &0 < H /\ L pow 2 + H pow 2 = &1 /\ H = (&8 / &11) * L /\
         &0 < c976ltm_f1 L H`,
  SUBGOAL_THEN `&0 < sqrt(&185) /\ sqrt(&185) pow 2 = &185` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SQRT_POS_LT THEN REAL_ARITH_TAC;
                    MATCH_MP_TAC SQRT_POW_2 THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  SPEC_TAC(`sqrt(&185)`,`d:real`) THEN GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1344 / &99 < d` ASSUME_TAC THENL
   [C976LTM_CONTRA THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
    C976LTM_PROD `&0 <= (&1344 / &99 - d) * (&1344 / &99 + d)` THEN C976LTM_LIN; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`&11 / d`; `&8 / d`] THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  SUBGOAL_THEN `~(d = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `d pow 2 = &185` THEN UNDISCH_TAC `~(d = &0)` THEN CONV_TAC REAL_FIELD;
    UNDISCH_TAC `~(d = &0)` THEN CONV_TAC REAL_FIELD;
    SUBGOAL_THEN `c976ltm_f1 (&11 / d) (&8 / d) = (&99 * d - &1344) / &3700` SUBST1_TAC THENL
     [REWRITE_TAC[c976ltm_f1] THEN
      UNDISCH_TAC `d pow 2 = &185` THEN UNDISCH_TAC `~(d = &0)` THEN CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC]]);;

(* Lean: left_high_margin *)
let C976LTM_LEFT_HIGH_MARGIN = prove
 (`forall l h. &0 < l /\ &0 < h /\ l pow 2 + h pow 2 = &1 /\ l / &2 <= h /\ h <= (&8 / &11) * l
         ==> &0 < (&37 / &100) * l + (&11 / &100) * h - &219 / &625 +
                  (&17 / &625) * l pow 2 - (&161 / &2500) * l * h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM c976ltm_f1] THEN
  X_CHOOSE_THEN `L:real` (X_CHOOSE_THEN `H:real` STRIP_ASSUME_TAC) C976LTM_HIGH_ENDPOINT THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `H * l = (&8 / &11) * (L * l)` ASSUME_TAC THENL
   [UNDISCH_TAC `H = (&8 / &11) * L` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C976LTM_PROD `&0 <= L * ((&8 / &11) * l - h)` THEN
  C976LTM_FACT `L * h <= H * l` THEN
  SUBGOAL_THEN `h <= H` ASSUME_TAC THENL
   [C976LTM_CONTRA THEN
    C976LTM_PROD `&0 < (h - H) * (h + H)` THEN
    SUBGOAL_THEN `l < L` ASSUME_TAC THENL
     [C976LTM_CONTRA THEN C976LTM_PROD `&0 <= (l - L) * (l + L)` THEN C976LTM_LIN; ALL_TAC] THEN
    C976LTM_PROD `&0 < L * (h - H)` THEN C976LTM_PROD `&0 < H * (L - l)` THEN C976LTM_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `L <= l` ASSUME_TAC THENL
   [C976LTM_CONTRA THEN
    C976LTM_PROD `&0 < (L - l) * (l + L)` THEN
    C976LTM_PROD `&0 <= (H - h) * (h + H)` THEN C976LTM_LIN;
    ALL_TAC] THEN
  C976LTM_PROD `&0 <= (H - h) * ((h + H) - (l + L) / &2)` THEN
  SUBGOAL_THEN `(H - h) / &2 <= l - L` ASSUME_TAC THENL
   [C976LTM_CONTRA THEN
    C976LTM_PROD `&0 < (l + L) * ((H - h) / &2 - (l - L))` THEN C976LTM_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `h <= &1` ASSUME_TAC THENL
   [C976LTM_CONTRA THEN C976LTM_PROD `&0 < (h - &1) * (h + &1)` THEN
    C976LTM_PROD `&0 <= l * l` THEN C976LTM_LIN; ALL_TAC] THEN
  C976LTM_PROD `&0 <= (l - L) * ((&37 / &100 + (&17 / &625) * (l + L) - (&161 / &2500) * h) -
                                   &3 / &10)` THEN
  C976LTM_PROD `&0 <= (H - h) * (&11 / &100 - (&11 / &100 - (&161 / &2500) * L))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c976ltm_f1; REAL_POW_2]) THEN
  REWRITE_TAC[c976ltm_f1; REAL_POW_2] THEN C976LTM_LIN);;

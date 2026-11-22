(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/BottomBoundaryMargin.lean           *)
(* (N12Compact.C1092MMMPBottomBoundaryMargin).  DOUBLE-RIGHT-BOTTOM-ORIGIN   *)
(* section 3: the actual boundary normal cannot separate.  Data:             *)
(* c1092bbo_data; half / half_identities: C1092WPS_half /                    *)
(* C1092MPIH_HALF_IDENTITIES; upper_nn: C1092MCSUP_UPPER_NN; upper: ABT_upper.*)
(* The boundary square R is written b t p q a (Lean R.c R.s R.loU R.loV).    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_BottomBoundaryOrder.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;

let C1092BBM_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092BBM_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBM_LIN_TAC; DISCH_TAC];;

let C1092BBM_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBM_LIN_TAC; DISCH_TAC];;

let C1092BBM_POS_OF_MUL = prove
 (`forall x y. &0 < x /\ &0 < x * y ==> &0 < y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:real`; `--y`] REAL_LE_MUL) THEN
  ASM_REWRITE_TAC[REAL_MUL_RNEG] THEN ASM_REAL_ARITH_TAC);;

(* Lean: low_scalar (private) *)
let C1092BBM_LOW_SCALAR = prove
 (`forall c s b t. c977cc_normal c s /\ &0 < s /\ &0 < b /\ &0 < t /\ b pow 2 + t pow 2 = &1 /\
             C1092WPS_half c s < &13 / &50 /\ &0 < t * c - b * s /\ &4 * t <= &3 * b
             ==> &1 < b * c + t * s + (t * c - b * s) * ((&7 / &20) * (c - s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  MP_TAC(SPECL [`b:real`; `t:real`] C1092MPIH_HALF_IDENTITIES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MPIH_HALF_IDENTITIES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092BBM_LIN_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `&0 < C1092WPS_half c s /\ &0 < C1092WPS_half b t` MP_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN
    CONJ_TAC THEN C1092BBM_LIN_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (find_term ((=) `C1092WPS_half`)) (concl th)))) THEN
  SPEC_TAC(`C1092WPS_half c s`,`z:real`) THEN SPEC_TAC(`C1092WPS_half b t`,`w:real`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  ABBREV_TAC `q = (&7 / &20) * (c - s)` THEN
  ABBREV_TAC `dl = t * c - b * s` THEN
  ABBREV_TAC `al = b * c + t * s` THEN
  (* bLower, tUpper, wUpper *)
  C1092BBM_LE_MUL_TAC `&3 * b - &4 * t` `&3 * b + &4 * t` THEN
  SUBGOAL_THEN `&4 / &5 <= b /\ t <= &3 / &5` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THENL
     [C1092BBM_LT_MUL_TAC `&4 / &5 - b` `&4 / &5 + b`;
      C1092BBM_LT_MUL_TAC `t - &3 / &5` `t + &3 / &5`] THEN
    C1092BBM_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `w <= &1 / &3` ASSUME_TAC THENL
   [C1092BBM_LE_MUL_TAC `w:real` `b - &4 / &5` THEN C1092BBM_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= q /\ q <= &7 / &20` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092BBM_LIN_TAC; ALL_TAC] THEN
  (* atThird *)
  SUBGOAL_THEN `(&1 + z * z) * (q * (&3 + z) - &1 + &3 * z) =
                &1 / &20 + (&5 / &4) * z - (&11 / &4) * z * z + (&53 / &20) * z * z * z`
    ASSUME_TAC THENL
   [UNDISCH_TAC `(&7 / &20) * (c - s) = q` THEN UNDISCH_TAC `z * (&1 + c) = s` THEN
    UNDISCH_TAC `s * z = &1 - c` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092BBM_LE_MUL_TAC `z:real` `&5 / &4 - (&11 / &4) * z` THEN
  SUBGOAL_THEN `&0 <= z * z * z` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [C1092BBM_LIN_TAC; MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C1092BBM_LIN_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < q * (&3 + z) - &1 + &3 * z` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092BBM_POS_OF_MUL THEN EXISTS_TAC `&1 + z * z` THEN
    MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
    CONJ_TAC THEN C1092BBM_LIN_TAC; ALL_TAC] THEN
  (* halfGap *)
  C1092BBM_LE_MUL_TAC `q:real` `&13 / &50 - z` THEN
  C1092BBM_LE_MUL_TAC `&1 / &3 - w` `&1 - q * z` THEN
  SUBGOAL_THEN `&0 < q * (&1 + z * w) - (w - z)` ASSUME_TAC THENL
   [C1092BBM_LIN_TAC; ALL_TAC] THEN
  (* relative identities *)
  SUBGOAL_THEN `&0 < al` ASSUME_TAC THENL
   [C1092BBM_LT_MUL_TAC `b:real` `c:real` THEN C1092BBM_LE_MUL_TAC `t:real` `s:real` THEN
    C1092BBM_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `dl * (&1 + z * w) = (&1 + al) * (w - z) /\ al * al + dl * dl = &1`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`t * c - b * s = dl`; `b * c + t * s = al`;
      `z * (&1 + c) = s`; `s * z = &1 - c`; `w * (&1 + b) = t`; `t * w = &1 - b`;
      `c * c + s * s = &1`; `b * b + t * t = &1`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN CONJ_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092BBM_LT_MUL_TAC `&1 + al` `q * (&1 + z * w) - (w - z)` THEN
  C1092BBM_LT_MUL_TAC `z:real` `w:real` THEN
  SUBGOAL_THEN `&0 < q * (&1 + al) - dl` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092BBM_POS_OF_MUL THEN EXISTS_TAC `&1 + z * w` THEN
    CONJ_TAC THENL [C1092BBM_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + z * w) * (q * (&1 + al) - dl) =
                  (&1 + al) * (q * (&1 + z * w) - (w - z))` SUBST1_TAC THENL
     [UNDISCH_TAC `dl * (&1 + z * w) = (&1 + al) * (w - z)` THEN CONV_TAC REAL_RING;
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  C1092BBM_LT_MUL_TAC `dl:real` `q * (&1 + al) - dl` THEN
  SUBGOAL_THEN `&0 < al + dl * q - &1` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092BBM_POS_OF_MUL THEN EXISTS_TAC `&1 + al` THEN
    CONJ_TAC THENL [C1092BBM_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 + al) * (al + dl * q - &1) = dl * (q * (&1 + al) - dl)` SUBST1_TAC THENL
     [UNDISCH_TAC `al * al + dl * dl = &1` THEN CONV_TAC REAL_RING; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  C1092BBM_LIN_TAC);;

(* Lean: high_scalar (private) *)
let C1092BBM_HIGH_SCALAR = prove
 (`forall c s b t. c977cc_normal c s /\ &2331 / &2669 < c /\ s < &1300 / &2669 /\
             &0 < b /\ &3 * b <= &4 * t
             ==> (&543 / &500) * b < b * c + t * s + (t * c - b * s) * ((&7 / &20) * (c - s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C1092BBM_LE_MUL_TAC `(&7 / &20) * (c - s)` `c:real` THEN
  C1092BBM_LE_MUL_TAC `t - (&3 / &4) * b` `s + ((&7 / &20) * (c - s)) * c` THEN
  C1092BBM_LT_MUL_TAC `c - &871 / &1000` `&1 - (&49 / &80) * s` THEN
  MP_TAC(SPEC `s:real` REAL_LE_SQUARE) THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < c + (&3 / &4) * s - &543 / &500 + &21 / &80 + (&7 / &80) * s * s -
                    (&49 / &80) * s * c` ASSUME_TAC THENL [C1092BBM_LIN_TAC; ALL_TAC] THEN
  C1092BBM_LT_MUL_TAC `b:real`
   `c + (&3 / &4) * s - &543 / &500 + &21 / &80 + (&7 / &80) * s * s - (&49 / &80) * s * c` THEN
  SUBGOAL_THEN
   `b * c + (&3 / &4) * b * s + ((&3 / &4) * b * c - b * s) * ((&7 / &20) * (c - s)) -
    (&543 / &500) * b =
    b * (c + (&3 / &4) * s - &543 / &500 + &21 / &80 + (&7 / &80) * s * s -
         (&49 / &80) * s * c)` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092BBM_LIN_TAC);;

(* Lean: lowerU_lt_one (private) *)
let C1092BBM_LOWERU_LT_ONE = prove
 (`forall cC sC uC vC aC b t p q a.
     b * b + t * t = &1 /\ &0 < a /\ &1 < a /\
     c1092bbo_data cC sC uC vC aC b t p q a
     ==> p < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092bbo_data] THEN STRIP_TAC THEN
  SUBGOAL_THEN `b < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092BBM_LE_MUL_TAC `b - &1` `b + &1` THEN C1092BBM_LT_MUL_TAC `t:real` `t:real` THEN
    C1092BBM_LIN_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `b <= &457 / &500` THENL [C1092BBM_LIN_TAC; ALL_TAC] THEN
  C1092BBM_LT_MUL_TAC `&1 - b` `(&543 / &500) * b - &457 / &500` THEN
  MP_TAC(SPECL [`t:real`; `q:real`; `--(&543 / &500) * t`] REAL_LT_LMUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBM_LIN_TAC; DISCH_TAC] THEN
  C1092BBM_LT_MUL_TAC `b:real` `a - &1` THEN
  SUBGOAL_THEN `b * p < b` ASSUME_TAC THENL [C1092BBM_LIN_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092BBM_LE_MUL_TAC `b:real` `p - &1` THEN C1092BBM_LIN_TAC);;

(* Lean: boundary_normal_impossible *)
let C1092BBM_BOUNDARY_NORMAL_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC b t p q a.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ b * b + t * t = &1 /\ &0 < a /\
     &1 < aC /\ aC = a /\ c977cc_normal cC sC /\
     &2331 / &2669 < cC /\ sC < &1300 / &2669 /\ &0 < sC /\
     C1092WPS_half cC sC < &13 / &50 /\ &0 <= uC /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     c1092bbo_data cC sC uC vC aC b t p q a /\
     ABT_upper cC sC uC vC aC b t <= p
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = a`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `b:real`; `t:real`; `p:real`; `q:real`; `aC:real`] C1092BBM_LOWERU_LT_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092bbo_data] o
    check (fun th -> can (term_match [] `c1092bbo_data a b c d e f g h i j`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `b:real`; `t:real`;
                `b * cC + t * sC`; `t * cC - b * sC`] C1092MCSUP_UPPER_NN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    C1092BBM_LT_MUL_TAC `b:real` `cC:real` THEN C1092BBM_LE_MUL_TAC `t:real` `sC:real` THEN
    C1092BBM_LIN_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `(&7 / &20) * (cC - sC) < vC + aC` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (&7 / &20) (&7 / &20)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092BBM_LT_MUL_TAC `b:real` `cC:real` THEN C1092BBM_LE_MUL_TAC `t:real` `sC:real` THEN
  C1092BBM_LT_MUL_TAC `b * cC + t * sC` `uC + aC - &1` THEN
  C1092BBM_LT_MUL_TAC `t * cC - b * sC` `vC + aC - (&7 / &20) * (cC - sC)` THEN
  ASM_CASES_TAC `&4 * t <= &3 * b` THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `b:real`; `t:real`] C1092BBM_LOW_SCALAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; DISCH_TAC] THEN C1092BBM_LIN_TAC;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `b:real`; `t:real`] C1092BBM_HIGH_SCALAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(&4 * t <= &3 * b)` THEN
                    REAL_ARITH_TAC; DISCH_TAC] THEN
    C1092BBM_LIN_TAC]);;

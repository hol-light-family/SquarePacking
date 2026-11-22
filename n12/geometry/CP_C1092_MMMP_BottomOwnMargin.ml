(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/BottomOwnMargin.lean                *)
(* (N12Compact.C1092MMMPBottomOwnMargin).  DOUBLE-RIGHT-BOTTOM-ORIGIN        *)
(* section 2.  Data: c1092bbo_data; lower: ABT_lower; lower_pn:              *)
(* C1092WS_LOWER_PN; strict_bounds: ABT_STRICT_BOUNDS.                        *)
(* The boundary square R is written b t p q a (Lean R.c R.s R.loU R.loV).    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_BottomBoundaryMargin.ml";;

let C1092BOM_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092BOM_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BOM_LIN_TAC; DISCH_TAC];;

let C1092BOM_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BOM_LIN_TAC; DISCH_TAC];;

let C1092BOM_NORMAL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal; REAL_POW_2] th))
    (filter (fun th -> can (term_match [] `c977cc_normal x y`) (concl th)) ths));;

(* Lean: large_cosine (private) *)
let C1092BOM_LARGE_COSINE = prove
 (`forall c s b t. c977cc_normal c s /\ &0 < b /\ &0 < t /\ b pow 2 + t pow 2 = &1 /\
             &0 < t * c - b * s /\ &457 / &500 <= b
             ==> c * b * (&2 - b - t) + s * (b pow 2 - b * t + (&457 / &500) * t) < b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092BOM_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  SUBGOAL_THEN `b < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092BOM_LE_MUL_TAC `b - &1` `b + &1` THEN C1092BOM_LT_MUL_TAC `t:real` `t:real` THEN
    C1092BOM_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t < &203 / &500` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092BOM_LE_MUL_TAC `b - &457 / &500` `b + &457 / &500` THEN
    C1092BOM_LE_MUL_TAC `t - &203 / &500` `t + &203 / &500` THEN C1092BOM_LIN_TAC; ALL_TAC] THEN
  ABBREV_TAC `K = &2 - b - t` THEN
  ABBREV_TAC `J = b * b - b * t + (&457 / &500) * t` THEN
  SUBGOAL_THEN `&0 < K` ASSUME_TAC THENL [C1092BOM_LIN_TAC; ALL_TAC] THEN
  C1092BOM_LE_MUL_TAC `b:real` `b - t` THEN
  SUBGOAL_THEN `&0 <= J` ASSUME_TAC THENL [C1092BOM_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= b * b` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  C1092BOM_LE_MUL_TAC `b * b` `K:real` THEN C1092BOM_LE_MUL_TAC `t:real` `J:real` THEN
  ABBREV_TAC `base = b * b * K + t * J` THEN
  SUBGOAL_THEN `&0 <= base` ASSUME_TAC THENL [C1092BOM_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `base - b = (b - &1) * ((&543 / &500) * b - &457 / &500) /\
                J - t * K = &1 - (&543 / &500) * t /\
                c * b * K + s * J = (b * c + t * s) * base - b * (t * c - b * s) * (J - t * K) /\
                (b * c + t * s) * (b * c + t * s) + (t * c - b * s) * (t * c - b * s) = &1`
    STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["base"; "K"; "J"] THEN
    UNDISCH_TAC `b * b + t * t = &1` THEN UNDISCH_TAC `c * c + s * s = &1` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THEN
    REPEAT(POP_ASSUM MP_TAC) THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092BOM_LT_MUL_TAC `&1 - b` `(&543 / &500) * b - &457 / &500` THEN
  C1092BOM_LT_MUL_TAC `b:real` `c:real` THEN C1092BOM_LE_MUL_TAC `t:real` `s:real` THEN
  SUBGOAL_THEN `b * c + t * s <= &1` ASSUME_TAC THENL
   [MP_TAC(SPEC `t * c - b * s` REAL_LE_SQUARE) THEN
    MP_TAC(SPEC `(b * c + t * s) - &1` REAL_LE_SQUARE) THEN REPEAT DISCH_TAC THEN
    C1092BOM_LIN_TAC; ALL_TAC] THEN
  C1092BOM_LE_MUL_TAC `&1 - (b * c + t * s)` `base:real` THEN
  C1092BOM_LT_MUL_TAC `b:real` `t * c - b * s` THEN
  C1092BOM_LT_MUL_TAC `b * (t * c - b * s)` `J - t * K` THEN
  C1092BOM_LIN_TAC);;

(* Lean: small_cosine (private) *)
let C1092BOM_SMALL_COSINE = prove
 (`forall c s b t. c977cc_normal c s /\ &500 / &543 < c /\ &0 < b /\ &0 < t /\
             b pow 2 + t pow 2 = &1 /\ b <= &457 / &500
             ==> c * t * (&2 - b - t) + s * b * (b + t - &457 / &500) < t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092BOM_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `s < &391 / &1000` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092BOM_LT_MUL_TAC `c - &500 / &543` `c + &500 / &543` THEN
    C1092BOM_LE_MUL_TAC `s - &391 / &1000` `s + &391 / &1000` THEN C1092BOM_LIN_TAC;
    ALL_TAC] THEN
  C1092BOM_LT_MUL_TAC `c:real` `t:real` THEN C1092BOM_LE_MUL_TAC `b:real` `t:real` THEN
  ASM_CASES_TAC `t <= b` THENL
   [SUBGOAL_THEN `&1 <= b + t` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092BOM_LT_MUL_TAC `&1 - b - t` `&1 + b + t` THEN C1092BOM_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1319 / &1000 < b + t` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092BOM_LE_MUL_TAC `&457 / &500 - b` `&457 / &500 - t` THEN
      C1092BOM_LE_MUL_TAC `b + t - &1` `&1319 / &1000 - b - t` THEN C1092BOM_LIN_TAC;
      ALL_TAC] THEN
    C1092BOM_LE_MUL_TAC `&457 / &500 - b` `b + t` THEN
    SUBGOAL_THEN `(&23 / &25) * c + (&2 / &5) * s < &251 / &250` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092BOM_LE_MUL_TAC `(&23 / &25) * c + (&2 / &5) * s - &251 / &250`
                          `(&23 / &25) * c + (&2 / &5) * s + &251 / &250` THEN
      MP_TAC(SPEC `(&2 / &5) * c - (&23 / &25) * s` REAL_LE_SQUARE) THEN DISCH_TAC THEN
      C1092BOM_LIN_TAC; ALL_TAC] THEN
    C1092BOM_LT_MUL_TAC `c * t` `&681 / &1000 - (&2 - b - t)` THEN
    C1092BOM_LE_MUL_TAC `s:real` `(&457 / &500) * t - b * (b + t - &457 / &500)` THEN
    C1092BOM_LT_MUL_TAC `t:real` `&1 - ((&681 / &1000) * c + (&457 / &500) * s)` THEN
    C1092BOM_LIN_TAC;
    SUBGOAL_THEN `b <= t` ASSUME_TAC THENL
     [UNDISCH_TAC `~(t <= b)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092BOM_LE_MUL_TAC `b:real` `(&1 + t) / &2 - b` THEN
    SUBGOAL_THEN `&0 <= b / &2 - &1 + t` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092BOM_LT_MUL_TAC `&1 + t` `--(b / &2 - &1 + t)` THEN C1092BOM_LIN_TAC; ALL_TAC] THEN
    C1092BOM_LE_MUL_TAC `c * t` `(&1 - b / &2) - (&2 - b - t)` THEN
    C1092BOM_LE_MUL_TAC `s:real` `b:real` THEN C1092BOM_LT_MUL_TAC `b:real` `t:real` THEN
    C1092BOM_LE_MUL_TAC `s * b` `&457 / &500 - b` THEN
    C1092BOM_LT_MUL_TAC `b * t` `c / &2 - s` THEN
    C1092BOM_LE_MUL_TAC `&1 - c` `t:real` THEN
    C1092BOM_LIN_TAC]);;

(* Lean: own_normal_impossible *)
let C1092BOM_OWN_NORMAL_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC b t p q a.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ b * b + t * t = &1 /\ &0 < a /\
     &1 < aC /\ aC = a /\ c977cc_normal cC sC /\ &0 < sC /\ &0 <= uC /\
     linside b t p q a (&543 / &500) (&0) /\
     c1092bbo_data cC sC uC vC aC b t p q a /\
     uC + aC <= ABT_lower b t p q a cC sC
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = a`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092bbo_data] o
    check (fun th -> can (term_match [] `c1092bbo_data a b c d e f g h i j`) (concl th))) THEN
  C1092BOM_NORMAL_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`; `p:real`; `q:real`; `aC:real`; `cC:real`; `sC:real`;
                `b * cC + t * sC`; `--(t * cC - b * sC)`] C1092WS_LOWER_PN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN
    C1092BOM_LT_MUL_TAC `b:real` `cC:real` THEN C1092BOM_LE_MUL_TAC `t:real` `sC:real` THEN
    C1092BOM_LIN_TAC;
    DISCH_TAC] THEN
  ABBREV_TAC `L = ABT_lower b t p q aC cC sC` THEN
  ABBREV_TAC `dl = t * cC - b * sC` THEN
  SUBGOAL_THEN `t * L = sC * p - aC * dl * (t + b) + dl * (b * (p + aC) - t * q)`
    ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th)))) THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  C1092BOM_LT_MUL_TAC `b:real` `t:real` THEN
  C1092BOM_LE_MUL_TAC `dl:real` `&2 - (b * (p + aC) - t * q)` THEN
  C1092BOM_LT_MUL_TAC `aC - &1` `dl:real` THEN
  C1092BOM_LT_MUL_TAC `(aC - &1) * dl` `t + b` THEN
  SUBGOAL_THEN `t * L < sC * p + dl * (&2 - b - t)` ASSUME_TAC THENL
   [C1092BOM_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `L < &1` ASSUME_TAC THENL
   [ASM_CASES_TAC `&457 / &500 <= b` THENL
     [MP_TAC(SPECL [`t:real`; `q:real`; `--(&543 / &500) * t`] REAL_LT_LMUL) THEN
      ANTS_TAC THENL [CONJ_TAC THEN C1092BOM_LIN_TAC; DISCH_TAC] THEN
      C1092BOM_LT_MUL_TAC `b:real` `aC - &1` THEN
      SUBGOAL_THEN `b * p < &2 - (&543 / &500) * t * t - b` ASSUME_TAC THENL
       [C1092BOM_LIN_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`b:real`; `t * L`; `sC * p + dl * (&2 - b - t)`] REAL_LT_LMUL) THEN
      ANTS_TAC THENL [CONJ_TAC THEN C1092BOM_LIN_TAC; DISCH_TAC] THEN
      MP_TAC(SPECL [`sC:real`; `b * p`; `&2 - (&543 / &500) * t * t - b`] REAL_LT_LMUL) THEN
      ANTS_TAC THENL [CONJ_TAC THEN C1092BOM_LIN_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN
       `sC * (&2 - (&543 / &500) * t * t - b) + b * dl * (&2 - b - t) =
        t * (cC * b * (&2 - b - t) + sC * (b pow 2 - b * t + (&457 / &500) * t))`
        ASSUME_TAC THENL
       [EXPAND_TAC "dl" THEN UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING;
        ALL_TAC] THEN
      MP_TAC(SPECL [`cC:real`; `sC:real`; `b:real`; `t:real`] C1092BOM_LARGE_COSINE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C1092BOM_LIN_TAC; DISCH_TAC] THEN
      MP_TAC(SPECL [`t:real`;
        `cC * b * (&2 - b - t) + sC * (b pow 2 - b * t + (&457 / &500) * t)`; `b:real`]
        REAL_LT_LMUL) THEN
      ANTS_TAC THENL [CONJ_TAC THEN C1092BOM_LIN_TAC; DISCH_TAC] THEN
      REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      C1092BOM_LE_MUL_TAC `b * t` `L - &1` THEN C1092BOM_LIN_TAC;
      ASM_CASES_TAC `cC <= &500 / &543` THENL
       [MP_TAC(SPECL [`b:real`; `t:real`; `p:real`; `q:real`; `aC:real`;
                      `&543 / &500`; `&0`; `cC:real`; `sC:real`] ABT_STRICT_BOUNDS) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
        STRIP_TAC THEN C1092BOM_LIN_TAC;
        MP_TAC(SPECL [`sC:real`; `p:real`; `(&543 / &500) * b`] REAL_LT_LMUL) THEN
        ANTS_TAC THENL [CONJ_TAC THEN C1092BOM_LIN_TAC; DISCH_TAC] THEN
        SUBGOAL_THEN `t * L < cC * t * (&2 - b - t) + sC * b * (b + t - &457 / &500)`
          ASSUME_TAC THENL
         [SUBGOAL_THEN `dl * (&2 - b - t) + sC * (&543 / &500) * b =
                        cC * t * (&2 - b - t) + sC * b * (b + t - &457 / &500)`
            ASSUME_TAC THENL [EXPAND_TAC "dl" THEN REAL_ARITH_TAC; ALL_TAC] THEN
          C1092BOM_LIN_TAC; ALL_TAC] THEN
        MP_TAC(SPECL [`cC:real`; `sC:real`; `b:real`; `t:real`] C1092BOM_SMALL_COSINE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN
                        REPEAT CONJ_TAC THEN C1092BOM_LIN_TAC; DISCH_TAC] THEN
        REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
        C1092BOM_LE_MUL_TAC `t:real` `L - &1` THEN C1092BOM_LIN_TAC]];
    ALL_TAC] THEN
  C1092BOM_LIN_TAC);;

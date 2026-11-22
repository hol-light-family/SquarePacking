(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4SoutheastSignSupports.lean   *)
(* (namespace N12Compact.Completion.OtherCases.C983.F4SoutheastSignSupports).*)
(* Whole-square comparisons (9)--(12) of C983-F4-TOP-ONLY-8208-ENDING 2.1.  *)
(* Lean lower (ABTransverse) is ABT_lower; SupportBands.lower_nn is          *)
(* OCSB_LOWER_NN; C1092WholeSupports.lower_nn / lower_pn are C1092WS_*.     *)
(* The OpenSquare invariants of E are explicit: c*c+s*s = 1, 0 < a.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_OtherCases_SupportBands.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

(* Lean: Data (structure) *)
let c983fss_data = new_definition
 `c983fss_data (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    &4 / &5 < c /\ c < &1 /\ &0 < s /\ s < &1 / &2 /\
    u < c - &1 /\ v < --(&7 / &20) * (c + s) /\
    (&13 / &50) * c < u + a /\ --(&13 / &50) * s < v + a`;;

(* Lean: coefficients (private) *)
let C983FSS_COEFFICIENTS = prove
 (`forall c s u v a. c983fss_data c s u v a
     ==> (&1 - c) * (&13 / &50 - (&37 / &50) * c) < &0 /\
         s - (&37 / &50) * c * s - &13 / &50 < &0 /\
         s * ((&37 / &50) * c - &1) < &0`,
  REWRITE_TAC[c983fss_data] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < (&1 - c) * ((&37 / &50) * c - &13 / &50) /\
                &0 < (c - &4 / &5) * s /\ &0 < s * (&1 - (&37 / &50) * c)`
    MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC]);;

let C983FSS_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C983FSS_COEFFICIENTS) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c983fss_data]) THEN
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o
    check (fun th -> is_conj(concl th))));;

let C983FSS_FORMULA_TAC th nx ny d e =
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; nx; ny; d; e] th) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY REAL_ARITH_TAC THEN NLIN_TAC [];
    DISCH_THEN SUBST1_TAC];;

let C983FSS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [FIRST [MATCH_MP_TAC REAL_LT_LMUL; MATCH_MP_TAC REAL_LE_LMUL;
            MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: negative_w *)
let C983FSS_NEGATIVE_W = prove
 (`forall c s u v a d r. c * c + s * s = &1 /\ &0 < a /\ c983fss_data c s u v a /\
                   &0 < d /\ &0 <= r /\ r <= d
     ==> ABT_lower c s u v a d (--r) < (&13 / &50) * r`,
  C983FSS_SETUP_TAC THEN
  C983FSS_PROD_TAC [`&0 < (c - s) * d`; `&0 <= s * (d - r)`;
                    `&0 <= c * r`; `&0 < s * d`] THEN
  C983FSS_FORMULA_TAC C1092WS_LOWER_PN `d:real` `--r` `c * d - s * r` `--(s * d + c * r)` THEN
  C983FSS_PROD_TAC [`(c * d - s * r) * u < (c * d - s * r) * (c - &1)`;
                    `(s * d + c * r) * (--(&13 / &50) * s) < (s * d + c * r) * (v + a)`;
                    `&0 < d * --((&1 - c) * (&13 / &50 - (&37 / &50) * c))`;
                    `&0 <= r * --(s - (&37 / &50) * c * s - &13 / &50)`] THEN
  SUBGOAL_THEN `d * (c * c + s * s) = d * &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  RASM_ARITH_TAC);;

(* Lean: positive_u *)
let C983FSS_POSITIVE_U = prove
 (`forall c s u v a d r. c * c + s * s = &1 /\ &0 < a /\ c983fss_data c s u v a /\
                   &0 < d /\ &0 <= r
     ==> ABT_lower c s u v a d r < &0`,
  C983FSS_SETUP_TAC THEN
  C983FSS_PROD_TAC [`&0 < c * d`; `&0 <= s * r`] THEN
  ASM_CASES_TAC `&0 <= c * r - s * d` THENL
   [C983FSS_FORMULA_TAC C1092WS_LOWER_NN `d:real` `r:real` `c * d + s * r` `c * r - s * d` THEN
    C983FSS_PROD_TAC [`(c * d + s * r) * u < (c * d + s * r) * &0`;
                      `&0 <= (c * r - s * d) * --v`] THEN
    RASM_ARITH_TAC;
    C983FSS_FORMULA_TAC C1092WS_LOWER_PN `d:real` `r:real` `c * d + s * r` `c * r - s * d` THEN
    C983FSS_PROD_TAC [`(c * d + s * r) * u < (c * d + s * r) * (c - &1)`;
                      `&0 <= --(c * r - s * d) * ((v + a) - --(&13 / &50) * s)`;
                      `&0 < d * --((&1 - c) * (&13 / &50 - (&37 / &50) * c))`;
                      `&0 <= r * --(s * ((&37 / &50) * c - &1))`] THEN
    SUBGOAL_THEN `d * (c * c + s * s) = d * &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RASM_ARITH_TAC]);;

(* Lean: positive_v *)
let C983FSS_POSITIVE_V = prove
 (`forall c s u v a d r. c * c + s * s = &1 /\ &0 < a /\ c983fss_data c s u v a /\
                   &0 < d /\ &0 <= r /\ r <= d
     ==> ABT_lower c s u v a r (--d) < (&13 / &50) * d`,
  C983FSS_SETUP_TAC THEN
  C983FSS_PROD_TAC [`&0 < c * d`; `&0 <= s * r`] THEN
  ASM_CASES_TAC `c * r - s * d <= &0` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `r:real`; `--d`]
      OCSB_LOWER_NN) THEN
    ANTS_TAC THENL [CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    C983FSS_PROD_TAC [`&0 <= --(c * r - s * d) * ((u + a) - (&13 / &50) * c)`;
                      `(c * d + s * r) * (--(&13 / &50) * s) < (c * d + s * r) * (v + a)`] THEN
    SUBGOAL_THEN `r * (c * c + s * s) = r * &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RASM_ARITH_TAC;
    C983FSS_FORMULA_TAC C1092WS_LOWER_PN `r:real` `--d` `c * r - s * d` `--(c * d + s * r)` THEN
    C983FSS_PROD_TAC [`&0 <= (c * r - s * d) * ((c - &1) - u)`;
                      `(c * d + s * r) * (--(&13 / &50) * s) < (c * d + s * r) * (v + a)`;
                      `&0 <= r * --((&1 - c) * (&13 / &50 - (&37 / &50) * c))`;
                      `&0 < d * --(s - (&37 / &50) * c * s - &13 / &50)`] THEN
    SUBGOAL_THEN `r * (c * c + s * s) = r * &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    RASM_ARITH_TAC]);;

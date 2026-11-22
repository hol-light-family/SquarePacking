(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/ShallowTopScalars   *)
(* .lean (namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.       *)
(* ShallowTopScalars).  CanonicalScalars.bounds: CCCS_BOUNDS.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalScalars.ml";;

(* Lean: pCoeff *)
let oltsts_pcoeff = new_definition
 `oltsts_pcoeff (l:real) (h:real) =
    &63 / &50 - l + h + (&43 / &500) * l pow 2 - (&27 / &100) * h pow 2 - (&1 / &25) * l * h`;;

(* Lean: qCoeff *)
let oltsts_qcoeff = new_definition
 `oltsts_qcoeff (l:real) (h:real) =
    l + h - &1 - (&89 / &250) * l * h - (&1 / &25) * l pow 2`;;

let OLTSTS_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [FIRST [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: central_bounds *)
let OLTSTS_CENTRAL_BOUNDS = prove
 (`forall l h. &0 < l /\ &0 <= h /\ h <= l /\ l pow 2 + h pow 2 = &1 /\
         (&2 / &3) * l < h /\ h < (&8 / &11) * l
     ==> &11 / &50 < l - h /\ &4 / &13 < h pow 2 /\ l pow 2 < &9 / &13 /\
         &6 / &13 < l * h`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  OLTSTS_PROD_TAC [`&0 < (&8 * l - &11 * h) * (&22 * l - &16 * h)`;
                   `&0 < (&3 * h - &2 * l) * (&3 * h + &2 * l)`;
                   `&0 < (&3 * h - &2 * l) * (&3 * l - &2 * h)`] THEN
  SUBGOAL_THEN `&11 / &50 < l - h` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    OLTSTS_PROD_TAC [`&0 <= (&11 / &50 - (l - h)) * (&11 / &50 + (l - h))`] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: coefficient_bounds *)
let OLTSTS_COEFFICIENT_BOUNDS = prove
 (`forall l h. &0 < l /\ &0 <= h /\ h <= l /\ l pow 2 + h pow 2 = &1 /\
         (&2 / &3) * l < h /\ h < (&8 / &11) * l
     ==> &1 / &500 < &1 - oltsts_pcoeff l h /\ &288 / &1625 < oltsts_qcoeff l h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `h:real`] OLTSTS_CENTRAL_BOUNDS) THEN
  MP_TAC(SPECL [`l:real`; `h:real`] CCCS_BOUNDS) THEN
  ASM_REWRITE_TAC[oltsts_pcoeff; oltsts_qcoeff] THEN
  UNDISCH_TAC `l pow 2 + h pow 2 = &1` THEN REAL_ARITH_TAC);;

(* Lean: ordinary_projection *)
let OLTSTS_ORDINARY_PROJECTION = prove
 (`forall l h. l pow 2 + h pow 2 = &1 /\ h <= (&8 / &11) * l
         ==> (&173 / &500) * l + (&6 / &5) * h < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(&11 * l + &8 * h) * (&11 * l + &8 * h) <= &185` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `&8 * l - &11 * h`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&6703 / &92500) * (&11 * l + &8 * h) < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(&11 * l + &8 * h) * (&11 * l + &8 * h) <= &185` THEN
    SPEC_TAC(`&11 * l + &8 * h`,`X:real`) THEN GEN_TAC THEN DISCH_TAC THEN
    NLIN_TAC []; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: residual *)
let oltsts_residual = new_definition
 `oltsts_residual (p:real) (q:real) (C:real) (S:real) =
    C + S - &1 + q * S pow 2 - p * C * S`;;

(* Lean: residual_positive *)
let OLTSTS_RESIDUAL_POSITIVE = prove
 (`forall p q C S. p < &1 /\ &1 / &6 < q /\ &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\
             C <= (&2 / &3) * S
     ==> S pow 2 / &30 < oltsts_residual p q C S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`S:real`; `C:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN ASM_REAL_ARITH_TAC;
                  STRIP_TAC] THEN
  OLTSTS_PROD_TAC [`&0 <= C * S`; `&0 < S * S`] THEN
  OLTSTS_PROD_TAC [`&0 <= (&1 - p) * (C * S)`; `&0 < (q - &1 / &6) * (S * S)`;
                   `&0 <= ((&2 / &3) * S - C) * S`] THEN
  REWRITE_TAC[oltsts_residual] THEN
  UNDISCH_TAC `C pow 2 + S pow 2 = &1` THEN REWRITE_TAC[REAL_POW_2] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: coefficient_residual_positive *)
let OLTSTS_COEFFICIENT_RESIDUAL_POSITIVE = prove
 (`forall l h C S. &0 < l /\ &0 <= h /\ h <= l /\ l pow 2 + h pow 2 = &1 /\
             (&2 / &3) * l < h /\ h < (&8 / &11) * l /\
             &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\ C <= (&2 / &3) * S
     ==> S pow 2 / &30 < oltsts_residual (oltsts_pcoeff l h) (oltsts_qcoeff l h) C S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `h:real`] OLTSTS_COEFFICIENT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC OLTSTS_RESIDUAL_POSITIVE THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

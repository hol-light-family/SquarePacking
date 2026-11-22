(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/OrdinaryLeftTop/ShallowTopExit      *)
(* Scalars.lean (namespace N12Compact.Completion.OtherCases.OrdinaryLeftTop.*)
(* ShallowTopExitScalars).  ORDINARY-LEFT-TOP-OBSTRUCTION Theorem 2, 2.1.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ShallowTopScalars.ml";;

(* Lean: F *)
let oltste_f = new_definition
 `oltste_f (C:real) = &7 / &20 - C + (&13 / &50) * C pow 2`;;

(* Lean: G *)
let oltste_g = new_definition
 `oltste_g (C:real) (S:real) = &13 / &20 - S + (&13 / &50) * C * S`;;

let OLTSTE_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [FIRST [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL;
            MATCH_MP_TAC REAL_LE_LMUL] THEN
     ASM_REAL_ARITH_TAC; ALL_TAC]) tms;;

(* Lean: wall_bounds *)
let OLTSTE_WALL_BOUNDS = prove
 (`forall C S. &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\ C <= (&2 / &3) * S
         ==> C <= &3 / &5 /\ &4 / &5 <= S /\ C <= &1 /\ S <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  OLTSTE_PROD_TAC [`&0 <= (&2 * S - &3 * C) * (&2 * S + &3 * C)`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C:real`; SQ_NONNEG `S - &1`]
   [`C <= &3 / &5`; `&4 / &5 <= S`; `S <= &1`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: cosine_lower *)
let OLTSTE_COSINE_LOWER = prove
 (`forall C S. &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\
         (&43 / &500) * S < (&13 / &50) * C
         ==> &31 / &100 < C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  OLTSTE_PROD_TAC [`&0 < (&130 * C - &43 * S) * (&130 * C + &43 * S)`] THEN
  NLIN_TAC []);;

(* Lean: chord (private) *)
let oltste_chord = new_definition
 `oltste_chord (C:real) = (&161 - &75 * C) / &145`;;

(* Lean: chord_below (private) *)
let OLTSTE_CHORD_BELOW = prove
 (`forall C S. &0 <= C /\ &0 <= S /\ C pow 2 + S pow 2 = &1 /\ &31 / &100 <= C /\ C <= &3 / &5
         ==> oltste_chord C <= S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oltste_chord; REAL_POW_2] THEN STRIP_TAC THEN
  OLTSTE_PROD_TAC [`&0 <= (&3 - &5 * C) * (&5330 * C - &1632)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  OLTSTE_PROD_TAC [`&0 < ((&161 - &75 * C) / &145 - S) * ((&161 - &75 * C) / &145 + S)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: combined_negative *)
let OLTSTE_COMBINED_NEGATIVE = prove
 (`forall C S. &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\ &31 / &100 <= C /\ C <= &3 / &5
         ==> oltste_g C S < &0 /\ oltste_f C + (&21 / &65) * oltste_g C S < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] OLTSTE_CHORD_BELOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[oltste_chord; oltste_f; oltste_g; REAL_POW_2] THEN DISCH_TAC THEN
  OLTSTE_PROD_TAC
   [`(&1 - (&13 / &50) * C) * ((&161 - &75 * C) / &145) <= (&1 - (&13 / &50) * C) * S`;
    `&0 <= (&3 / &5 - C) * (&15 / &29 + (&13 / &50) * (&161 / &145) -
                            (&13 / &50) * (&15 / &29) * (C + &3 / &5))`;
    `&0 <= (C - &31 / &100) * --((&157 / &725) * (C + &31 / &100) - &348547 / &471250 + &1 / &2)`] THEN
  CONJ_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: upper_exit_residual *)
let OLTSTE_UPPER_EXIT_RESIDUAL = prove
 (`forall l h C S. &0 < l /\ (&21 / &65) * l <= h /\ &0 <= C /\ &0 < S /\ C pow 2 + S pow 2 = &1 /\
             &31 / &100 <= C /\ C <= &3 / &5
     ==> l * oltste_f C + h * oltste_g C S < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`C:real`; `S:real`] OLTSTE_COMBINED_NEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`oltste_f C`,`f:real`) THEN SPEC_TAC(`oltste_g C S`,`g:real`) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OLTSTE_PROD_TAC [`&0 <= (h - (&21 / &65) * l) * --g`;
                   `&0 < l * --(f + (&21 / &65) * g)`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: marker_projection *)
let OLTSTE_MARKER_PROJECTION = prove
 (`forall C S. C pow 2 + S pow 2 = &1 ==> (&61 / &100) * C + (&13 / &20) * S < &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_POW_2] THEN DISCH_TAC THEN
  NLIN_TAC [SQ_NONNEG `(&13 / &20) * C - (&61 / &100) * S`;
            SQ_NONNEG `(&61 / &100) * C + (&13 / &20) * S - &1`]);;

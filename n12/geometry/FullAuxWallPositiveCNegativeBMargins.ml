(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveCNegativeBMargins.lean        *)
(* (Jatloe, N12-jatloe; namespace                                            *)
(*  N12Compact.FullAuxWallPositiveCNegativeBMargins).                        *)
(* Exact continuous margins for both corner escapes of the negative outer    *)
(* square, via rational disk bounds.                                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let FAWPCNB_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPCNB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: deficit (private) *)
let FAWPCNB_DEFICIT = prove
 (`forall b t. c977cc_normal b t ==> &1 - b <= (&3 / &5) * t pow 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN FAWPCNB_NORMAL_TAC THEN
  FAWPCNB_PROD_TAC `&1 - b` `&3 * b - &2` THEN NLIN_TAC ~deg2:false []);;

(* Lean: lower_u *)
let FAWPCNB_LOWER_U = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t
     ==> C * (&2 - b - t + (&3 / &5) * b * t) +
         S * ((&3 / &5) - b + t - (&3 / &5) * t pow 2) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] FAWPCNB_DEFICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FAWPCNB_NORMAL_TAC THEN
  FAWPCNB_PROD_TAC `b + t - &1` `&3 / &2 - (b + t)` THEN
  NLIN_FACTS_TAC [] [`(&4 / &5) * b * t <= b + t - &1`] THEN
  SUBGOAL_THEN `&2 - b - t + (&3 / &5) * b * t <= &1 - (&1 / &5) * b * t /\
                (&3 / &5) - b + t - (&3 / &5) * t pow 2 <= t - &2 / &5`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `t <= &2 / &5` THENL
  [FAWPCNB_PROD_TAC `b:real` `t:real` THEN
   FAWPCNB_PROD_TAC `C:real` `&1 - (&2 - b - t + (&3 / &5) * b * t)` THEN
   FAWPCNB_PROD_TAC `S:real` `--((&3 / &5) - b + t - (&3 / &5) * t pow 2)` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  FAWPCNB_PROD_TAC `b:real` `t - &2 / &5` THEN
  SUBGOAL_THEN `&2 - b - t + (&3 / &5) * b * t <= &189 / &200 /\
                (&3 / &5) - b + t - (&3 / &5) * t pow 2 <= &11 / &35`
  STRIP_ASSUME_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C - &189 / &200`; SQ_NONNEG `S - &11 / &35`]
    [`(&189 / &200) * C + (&11 / &35) * S < &1`] THEN
  FAWPCNB_PROD_TAC `C:real` `&189 / &200 - (&2 - b - t + (&3 / &5) * b * t)` THEN
  FAWPCNB_PROD_TAC `S:real` `&11 / &35 - ((&3 / &5) - b + t - (&3 / &5) * t pow 2)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: upper_v *)
let FAWPCNB_UPPER_V = prove
 (`forall C S b t. c977cc_normal C S /\ c977cc_normal b t
     ==> C * (&2 - b - (&13 / &20) * t pow 2 - (&13 / &20) * b * t) +
         S * (--(&1 / &20) + (&13 / &20) * t pow 2 - (&13 / &20) * b * t + t) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`] FAWPCNB_DEFICIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN FAWPCNB_NORMAL_TAC THEN
  FAWPCNB_PROD_TAC `t:real` `b - &7 / &10` THEN
  NLIN_FACTS_TAC [SQ_NONNEG `t:real`]
    [`&2 - b - (&13 / &20) * t pow 2 - (&13 / &20) * b * t <= &1 - (&9 / &20) * t`] THEN
  FAWPCNB_PROD_TAC `t:real` `b - t` THEN
  SUBGOAL_THEN `--(&1 / &20) + (&13 / &20) * t pow 2 - (&13 / &20) * b * t + t
                <= t - &1 / &20` ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  ASM_CASES_TAC `t <= &1 / &20` THENL
  [FAWPCNB_PROD_TAC `C:real`
     `&1 - (&2 - b - (&13 / &20) * t pow 2 - (&13 / &20) * b * t)` THEN
   FAWPCNB_PROD_TAC `S:real`
     `--(--(&1 / &20) + (&13 / &20) * t pow 2 - (&13 / &20) * b * t + t)` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  FAWPCNB_PROD_TAC `t:real` `&5 / &7 - t` THEN
  NLIN_FACTS_TAC [] [`(&1 - (&9 / &20) * t) pow 2 + (t - &1 / &20) pow 2 < &1`] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `C - (&1 - (&9 / &20) * t)`; SQ_NONNEG `S - (t - &1 / &20)`]
    [`(&1 - (&9 / &20) * t) * C + (t - &1 / &20) * S < &1`] THEN
  FAWPCNB_PROD_TAC `C:real`
    `(&1 - (&9 / &20) * t) - (&2 - b - (&13 / &20) * t pow 2 - (&13 / &20) * b * t)` THEN
  FAWPCNB_PROD_TAC `S:real`
    `(t - &1 / &20) - (--(&1 / &20) + (&13 / &20) * t pow 2 - (&13 / &20) * b * t + t)` THEN
  NLIN_TAC ~deg2:false []);;

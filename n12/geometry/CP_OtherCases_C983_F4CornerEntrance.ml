(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4CornerEntrance.lean          *)
(* (N12Compact.Completion.OtherCases.C983).  Actual F4 corner-root entrance. *)
(* Conventions of CP_OtherCases_C983_C974LocalEnding.ml / F4Filters.ml       *)
(* (statements c983sa_stmt; owners p 0 / 1 / 7 = owner 1 / 2 / 2304;         *)
(* 4 IN actual p 7 is c983f4f_mem 4 7).  ExactMarkers from OO_MARKERS;       *)
(* SingletonMissing.one/zero_missing_points CCSM_ONE/ZERO_MISSING_POINTS;    *)
(* C974LocalEnding.left_missing_corner_excluded_of_seeds                     *)
(* C983LE_LEFT_MISSING_CORNER_EXCLUDED_OF_SEEDS; F4MergedCenter.             *)
(* center_of_singleton_corner C983FMCE_CENTER_OF_SINGLETON_CORNER.           *)
(* (Lean header: "no compiler acceptance is asserted".)  Tag C983FCE_.       *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974LocalEnding.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4MergedCenterEnding.ml";;

(* the SingletonMissing seeds of the singleton owner m in {1, 2} *)
let C983FCE_SINGLETON_TAC m th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THEN ASM_SIMP_TAC[OO_UNIT; OO_BOX] THEN
  MP_TAC(SPECL C983E_VARS OO_SIDE) THEN MP_TAC(SPECL C983E_VARS OO_SIDE_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  MP_TAC(SPECL (C983E_VARS @ [C983E_F; mk_small_numeral m]) OO_MARKERS) THEN
  ASM_REWRITE_TAC[in_fam m C983E_F] THEN
  REWRITE_TAC[bitset_bits m; IN_SET_OF_LIST; MEM];;

let C983FCE_SEEDS_ONE = prove
 (c983sa_stmt [mk_neg (c983ab_in 2 `&1` `&1`)]
    (mk_conj(c983ab_in 2 `&1` `&91 / &50`, c983ab_in 2 `&19 / &25` `&49 / &25`)),
  C983FCE_SINGLETON_TAC 2 CCSM_ONE_MISSING_POINTS);;
let C983FCE_SEEDS_ZERO = prove
 (c983sa_stmt [mk_neg (c983ab_in 1 `&1` `&1`)]
    (mk_conj(c983ab_in 1 `&91 / &50` `&1`, c983ab_in 1 `&49 / &25` `&19 / &25`)),
  C983FCE_SINGLETON_TAC 1 CCSM_ZERO_MISSING_POINTS);;

(* Lean: f4_left_singleton_corner *)
let C983FCE_F4_LEFT_SINGLETON_CORNER = prove
 (c983sa_stmt [c983f4f_mem 4 7] (c983ab_in 2 `&1` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL C983E_VARS C983FCE_SEEDS_ONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL C983E_VARS C983LE_LEFT_MISSING_CORNER_EXCLUDED_OF_SEEDS) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: f4_bottom_singleton_seeds *)
let C983FCE_F4_BOTTOM_SINGLETON_SEEDS = prove
 (c983sa_stmt [c983f4f_mem 4 7]
    (list_mk_conj [mk_neg (c983ab_in 1 `&1` `&1`); c983ab_in 1 `&91 / &50` `&1`;
                   c983ab_in 1 `&49 / &25` `&19 / &25`]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C983E_VARS C983FCE_F4_LEFT_SINGLETON_CORNER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (c983ab_in 1 `&1` `&1`)) ASSUME_TAC THENL
   [MP_TAC(SPECL [`&1`; `&1`]
      (REWRITE_RULE[ldisj] (MP (SPECL C983E_VARS (oo_apart C983E_F 1 2)) (c983f4f_hh ())))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL C983E_VARS C983FCE_SEEDS_ZERO) THEN ASM_REWRITE_TAC[]);;

(* Lean: f4_merged_center *)
let C983FCE_F4_MERGED_CENTER = prove
 (c983sa_stmt [c983f4f_mem 4 7] (c983ab_in 2304 `&2` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C983E_VARS C983FCE_F4_LEFT_SINGLETON_CORNER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C983E_VARS C983FMCE_CENTER_OF_SINGLETON_CORNER) THEN ASM_REWRITE_TAC[]);;

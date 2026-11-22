(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C896Centers.lean                  *)
(* (namespace N12Compact.FiniteCases.C896Ending; Lean header: "uncompiled   *)
(* source").  Two actual C896 owners contain the container center, so the   *)
(* original C896 family is impossible.  owner p m is the 5-tuple (ooc .. m)  *)
(* .. l; seed_point / aux_point / foreign / bottom_marker / bottom_g5 /      *)
(* merged_g6_point: C896MergedInward (C896MI_ prefix); C896CentralPoints.fixed:    *)
(* C896CP_*; ClosedFrames.canonical_frame: CLF_CANONICAL_FRAME;              *)
(* MergedLeftNegative.point: MLN_POINT; CentralWallCenter.point: CWC_POINT;  *)
(* pullX / pullSwap: LINSIDE_PULLX / LINSIDE_PULLSW.  For the assembly the   *)
(* whole-case theorem is turned into |- EXCLUDED_ROW 483 (row of case 896).  *)
(* Tag C896CE_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C896MergedInward.ml";;
needs "n12/geometry/MergedLeftNegative.ml";;
needs "n12/geometry/CentralWallCenter.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/RowIdentity.ml";;

let C896CE_LOW = c896mi_seed_point 1 (`&87 / &50`, `&1`);;
let C896CE_TOP = c896mi_aux_point 16384 18;;
let C896CE_BOTTOM_F6 = c896mi_aux_point 8192 6;;
let C896CE_SINGLETON = c896mi_seed_point 2 (`&1`, `&87 / &50`);;
let C896CE_NE_SINGLETON = c896mi_seed_point 16 (`&113 / &50`, `&3`);;

let C896CE_HAVE tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;

(* Lean: merged_center *)
let C896CE_MERGED_CENTER = prove
 (c896mi_stmt [] (c896wb_own 768 `&2` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun th -> MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC)
    [C896CP_SW_MARKER; C896CP_SE_MARKER; C896MI_MERGED_G6_POINT] THEN
  MP_TAC (SPECL (c896wb_pullsw (c896wb_q 768)) CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_SIMP_TAC[OO_UNIT] THEN
    MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cA:real` (X_CHOOSE_THEN `sA:real` (X_CHOOSE_THEN `uA:real`
    (X_CHOOSE_THEN `vA:real` (X_CHOOSE_THEN `aA:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = l`)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[LINSIDE_PULLSW]) THEN
  SUBGOAL_THEN `linside cA sA uA vA l (&2) (&2)` MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  C896CE_HAVE `linside cA sA uA vA l (&33 / &20) (&33 / &20) /\
               linside cA sA uA vA l (&33 / &20) (&47 / &20) /\
               linside cA sA uA vA l (&2) (&113 / &50)` (ASM_REWRITE_TAC[]) THEN
  ASM_CASES_TAC `&0 <= sA` THENL
   [UNDISCH_TAC `linside cA sA uA vA l (&33 / &20) (&33 / &20) /\
                 linside cA sA uA vA l (&33 / &20) (&47 / &20) /\
                 linside cA sA uA vA l (&2) (&113 / &50)` THEN
    REWRITE_TAC[linside] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MLN_POINT THEN
  MAP_EVERY EXISTS_TAC (c896wb_pullsw (c896wb_q 8192)) THEN
  ASM_REWRITE_TAC[LINSIDE_PULLSW; ldisj] THEN
  REPEAT CONJ_TAC THEN
  FIRST [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC;
         MATCH_MP_TAC LCONT_PULLSW THEN ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
         MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
         ASM_SIMP_TAC[C896MI_BOTTOM_MARKER; C896CE_BOTTOM_F6] THEN NO_TAC;
         C896MI_FOREIGN_TAC 1 C896CE_LOW;
         C896MI_FOREIGN_TAC 8192 C896MI_BOTTOM_G5;
         C896MI_FOREIGN_TAC 16384 C896CE_TOP;
         MP_TAC (SPEC_ALL (oo_apart C896D_F 768 8192)) THEN ASM_REWRITE_TAC[ldisj] THEN
         DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: northwest_center *)
let C896CE_NORTHWEST_CENTER = prove
 (c896mi_stmt [] (c896wb_own 2048 `&2` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C896MI_USE_TAC CWC_POINT (c896wb_pullx (c896wb_q 2048) @ c896wb_pullx (c896wb_q 4096) @
                            c896wb_pullx (c896wb_q 32768))
    [C896CP_NW_F5; C896CP_NW_G3; C896CP_NW_MARKER; C896CP_LEFT_MARKER; C896CP_LEFT_G1;
     C896CP_TOP_MARKER; C896CP_TOP_F3]
    [768, C896CP_SW_MARKER; 1024, C896CP_NE_MARKER; 2, C896CE_SINGLETON; 16, C896CE_NE_SINGLETON]
    [MATCH_MP_TAC LCONT_PULLX THEN ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
     REWRITE_TAC[ldisj; LINSIDE_PULLX] THEN
     FIRST (map (fun n -> MP_TAC (SPEC_ALL (oo_apart C896D_F 2048 n)) THEN
                          ASM_REWRITE_TAC[ldisj] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC)
                [4096; 32768])] THEN
  DISCH_THEN ACCEPT_TAC);;

(* Lean: impossible *)
let C896CE_IMPOSSIBLE = prove
 (c896mi_stmt [] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL (oo_apart C896D_F 768 2048)) THEN ASM_REWRITE_TAC[ldisj] THEN
  DISCH_THEN (MP_TAC o SPECL [`&2`; `&2`]) THEN
  ASM_SIMP_TAC[C896CE_MERGED_CENTER; C896CE_NORTHWEST_CENTER]);;

(* the case exclusion and the row of case 896 for the assembly *)
let C896CE_EXCLUDES = prove
 (`excl_case 896`,
  REWRITE_TAC[ri_excludes_case_iff 483 `c896d_family`; excl_fam] THEN
  MESON_TAC[C896CE_IMPOSSIBLE]);;

let C896CE_EXCLUDED_ROW = ri_excluded_row 483 C896CE_EXCLUDES;;

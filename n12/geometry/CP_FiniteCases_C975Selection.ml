(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975Selection.lean                *)
(* (namespace N12Compact.FiniteCases.C975Selection; Lean header: "Source     *)
(* only").  The raw C1090 northeast selection on the C975 family.  owner p m *)
(* is the 5-tuple (ooc .. m) .. l; auxiliaries p m is ooaux .. m;            *)
(* natAuxOwners p 1 (ownerIndex p m) is auxown 1 (c1 (oidx ..)) .. l.        *)
(* C1090.NESelection.Input / selection: occ1090nes_input /                   *)
(* OCC1090NES_SELECTION; C975SelectionSeeds: C975SS_ prefix; the private     *)
(* g_combined is C975E_G_COMBINED; C975IncomingCut.top_g_options:            *)
(* C975IC_TOP_G_OPTIONS.  Tag C975SEL_.                                      *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975SelectionSeeds.ml";;
needs "n12/geometry/CP_OtherCases_C1090_NESelection.ml";;

(* the bar of C975SS_BOTTOM_REACH at a point *)
let C975SEL_BOTTOM_BAR = prove
 (`forall c1 c2 a b l x. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c975d_family /\
     &113 / &50 <= x /\ x <= &14 / &5
     ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l x (&1)`,
  REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL C975SS_BOTTOM_REACH) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

let C975SEL_INPUT_TM =
  list_mk_comb(`occ1090nes_input`, (fst (chop_list 4 (c975ic_owner 512))) @ [`l:real`] @
                                   (fst (chop_list 4 (c975ic_owner 1024))) @ [`l:real`]);;

(* Lean: selection_input *)
let C975SEL_SELECTION_INPUT = prove
 (c975ic_stmt [] C975SEL_INPUT_TM,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C975IC_COMPULSORY_TAC THEN
  REWRITE_TAC[occ1090nes_input] THEN REPEAT CONJ_TAC THEN
  FIRST [MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
         ASM_SIMP_TAC[oo_apart C975D_F 512 1024] THEN NO_TAC;
         ASM_SIMP_TAC[C975SS_SE_MARKER; C975SS_SE_F8; C975SS_SOUTHEAST_G8_POINT; C975SS_NE_MARKER] THEN NO_TAC;
         ASM_REWRITE_TAC C975IC_AUXPTS THEN NO_TAC;
         C975IC_FOREIGN_TAC 12 C975SS_SE_CORNER;
         C975IC_FOREIGN_TAC 12 C975SS_SE_CORNER_RIGHT;
         C975IC_FOREIGN_TAC 16384 C975SS_RIGHT_MARKER;
         C975IC_FOREIGN_TAC 34816 C975SS_NW_MARKER;
         C975IC_FOREIGN_TAC 16384 C975SS_RIGHT_F9;
         C975IC_FOREIGN_TAC 16384 C975SS_RIGHT_G9;
         X_GEN_TAC `x:real` THEN DISCH_TAC THEN DISCH_TAC THEN
         C975IC_FOREIGN_TAC 8192 C975SEL_BOTTOM_BAR]);;

(* Lean: northeast_selection *)
let C975SEL_NORTHEAST_SELECTION = prove
 (c975ic_stmt [] (mk_conj(c975ic_own 1024 `&113 / &50` `&3`,
                          mk_imp(c975ic_own 1024 `&113 / &50` `&2`, c975ic_own 1024 `&12 / &5` `&3`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OCC1090NES_SELECTION THEN
  MAP_EVERY EXISTS_TAC (fst (chop_list 4 (c975ic_owner 512)) @ [`l:real`]) THEN
  ASM_SIMP_TAC[C975SEL_SELECTION_INPUT; OO_UNIT] THEN
  MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: northeast_g7 *)
let C975SEL_NORTHEAST_G7 = prove
 (c975ic_stmt [] (c975ic_mem 17 1024),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM (oo_aux_point 17)] THEN
  ASM_SIMP_TAC[C975SEL_NORTHEAST_SELECTION]);;

(* Lean: northeast_g6_f7 *)
let C975SEL_NORTHEAST_G6_F7 = prove
 (c975ic_stmt [c975ic_mem 16 1024] (c975ic_mem 7 1024),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM (oo_aux_point 7)] THEN
  MP_TAC (SPEC_ALL C975SEL_NORTHEAST_SELECTION) THEN ASM_REWRITE_TAC[] THEN
  ASM_REWRITE_TAC C975IC_AUXPTS THEN SIMP_TAC[]);;

(* Lean: not_top_g7 *)
let C975SEL_NOT_TOP_G7 = prove
 (c975ic_stmt [] (mk_neg (c975ic_mem 17 34816)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C975SEL_NORTHEAST_G7) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OO_EXCLUDE_ALL_TAC C975D_F 34816 THEN ASM_REWRITE_TAC[]);;

(* Lean: top_g_exact *)
let C975SEL_TOP_G_EXACT = prove
 (c975ic_stmt [] (mk_eq(c975ic_gown 34816, `{4}`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C975IC_TOP_G_OPTIONS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC (TAUT `false ==> p`) THEN
  MP_TAC (SPEC_ALL C975SEL_NOT_TOP_G7) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC (mk_eq(c975ic_gown 34816, `{4,7}`)) THEN
  REWRITE_TAC[EXTENSION; C975E_G_COMBINED] THEN DISCH_THEN(MP_TAC o SPEC `7`) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC TAUT);;

(* Lean: not_top_f7 *)
let C975SEL_NOT_TOP_F7 = prove
 (c975ic_stmt [] (mk_neg (c975ic_mem 7 34816)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN C975IC_COMPULSORY_TAC THEN
  SUBGOAL_THEN (c975ic_own 34816 `&113 / &50` `&3`) ASSUME_TAC THENL
   [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&87 / &50`; `&12 / &5`] THEN
    ASM_REWRITE_TAC C975IC_AUXPTS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC (SPEC_ALL (oo_apart C975D_F 34816 1024)) THEN ASM_REWRITE_TAC[ldisj] THEN
  DISCH_THEN (MP_TAC o SPECL [`&113 / &50`; `&3`]) THEN
  ASM_SIMP_TAC[C975SEL_NORTHEAST_SELECTION]);;

(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975SelectionSeeds.lean           *)
(* (namespace N12Compact.FiniteCases.C975Selection; Lean header: "Source     *)
(* only, uncompiled").  C1090's initial crosspoint and southeast selection   *)
(* reductions on the C975 family.  owner p m is the 5-tuple (ooc .. m) ..    *)
(* l; seed_point / aux_point / foreign are the producers c975ss_seed_point   *)
(* (= oo_seed), c975ss_aux_point (= c975ic_aux at compulsory points,         *)
(* OO_AUX_EXACT in general) and C975IC_FOREIGN_TAC.  The structure Fixed is  *)
(* the predicate c975ss_fixed.  C981CompletionCrosspoint.point: C981CP_POINT;*)
(* ElbowPoint.points_original: OCEP_POINTS_ORIGINAL; C1089.ContinuousBottom. *)
(* reach: C1089CB_REACH.  Tag C975SS_.                                       *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975IncomingCut.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;

let c975ss_pully = c975ic_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let c975ss_pullsw = c975ic_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* Lean: seed_point *)
let c975ss_seed_point m p = c975ic_seed m p;;
(* Lean: aux_point (at a compulsory point of C975Entrance.compulsory) *)
let c975ss_aux_point m j = c975ic_aux m j;;

let C975SS_SW_MARKER = c975ss_seed_point 256 (`&33 / &20`, `&33 / &20`);;
let C975SS_SW_F4 = c975ss_aux_point 256 4;;
let C975SS_SW_G3 = c975ss_aux_point 256 13;;
let C975SS_SE_MARKER = c975ss_seed_point 512 (`&47 / &20`, `&33 / &20`);;
let C975SS_SE_F8 = c975ss_aux_point 512 8;;
let C975SS_NE_MARKER = c975ss_seed_point 1024 (`&47 / &20`, `&47 / &20`);;
let C975SS_NW_MARKER = c975ss_seed_point 34816 (`&33 / &20`, `&47 / &20`);;
let C975SS_TOP_MARKER = c975ss_seed_point 34816 (`&2`, `&1543 / &500`);;
let C975SS_BOTTOM_MARKER = c975ss_seed_point 8192 (`&2`, `&457 / &500`);;
let C975SS_BOTTOM_F6 = c975ss_aux_point 8192 6;;
let C975SS_BOTTOM_G5 = c975ss_aux_point 8192 15;;
let C975SS_RIGHT_MARKER = c975ss_seed_point 16384 (`&1543 / &500`, `&2`);;
let C975SS_RIGHT_F9 = c975ss_aux_point 16384 9;;
let C975SS_RIGHT_G9 = c975ss_aux_point 16384 19;;
let C975SS_SE_CORNER = c975ss_seed_point 12 (`&3`, `&1`);;
let C975SS_SE_CORNER_RIGHT = c975ss_seed_point 12 (`&1543 / &500`, `&1`);;

let C975SS_FIXED_THMS =
  [C975SS_SW_MARKER; C975SS_SW_F4; C975SS_SW_G3; C975SS_SE_MARKER; C975SS_SE_F8; C975SS_NE_MARKER;
   C975SS_NW_MARKER; C975SS_TOP_MARKER; C975SS_BOTTOM_MARKER; C975SS_BOTTOM_F6; C975SS_BOTTOM_G5;
   C975SS_RIGHT_MARKER; C975SS_RIGHT_F9; C975SS_RIGHT_G9; C975SS_SE_CORNER; C975SS_SE_CORNER_RIGHT];;

(* Lean: Fixed (structure) *)
let c975ss_fixed =
  let body = list_mk_conj (map (fun th -> rand (snd (strip_forall (concl th)))) C975SS_FIXED_THMS) in
  new_definition (mk_eq(list_mk_comb(`c975ss_fixed:(num->real)->(num->real)->(num->real)->(num->real)->real->bool`,
                                      C975IC_V5), body));;

(* Lean: fixed *)
let C975SS_FIXED = prove
 (c975ic_stmt [] `c975ss_fixed c1 c2 a b l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c975ss_fixed] THEN ASM_SIMP_TAC C975SS_FIXED_THMS);;

let C975SS_H1 = c975ss_seed_point 1 (`&28 / &25`, `&1`);;
let C975SS_H2 = c975ss_seed_point 1 (`&87 / &50`, `&1`);;
let C975SS_V1 = c975ss_seed_point 2 (`&1`, `&28 / &25`);;
let C975SS_V2 = c975ss_seed_point 2 (`&1`, `&87 / &50`);;

(* Lean: singleton_horizontal *)
let C975SS_SINGLETON_HORIZONTAL = prove
 (`forall c1 c2 a b l x. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c975d_family /\
     &28 / &25 <= x /\ x <= &87 / &50
     ==> linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l x (&1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_SIMP_TAC[C975SS_H1; C975SS_H2] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: singleton_vertical *)
let C975SS_SINGLETON_VERTICAL = prove
 (`forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c975d_family /\
     &28 / &25 <= y /\ y <= &87 / &50
     ==> linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l (&1) y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_SIMP_TAC[C975SS_V1; C975SS_V2] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* instances of the singleton bars *)
let c975ss_bar th t =
  let th1 = SPEC t (SPECL C975IC_V5 th) in
  let hyp = lhand (concl th1) in
  let h = ASSUME (lhand (concl (SPECL C975IC_V5 (c975ic_aux 512 8)))) in
  let ineqs = CONJ (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (rand (rand hyp)))))
                   (EQT_ELIM (REAL_RAT_REDUCE_CONV (rand (rand (rand hyp))))) in
  GENL C975IC_V5 (DISCH (concl h) (MP th1 (CONJ (CONJUNCT1 h) (CONJ (CONJUNCT2 h) ineqs))));;

(* Lean: southwest_south *)
let C975SS_SOUTHWEST_SOUTH = prove
 (c975ic_stmt [] (c975ic_own 256 `&2` `&3 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975IC_APPLY_TAC C981CP_POINT (c975ss_pully (c975ic_pullx (c975ic_owner 256)))
   [C975SS_SW_F4; C975SS_SW_G3; C975SS_SW_MARKER]
   [34816, C975SS_NW_MARKER; 512, C975SS_SE_MARKER;
    2, c975ss_bar C975SS_SINGLETON_VERTICAL `&8 / &5`;
    2, c975ss_bar C975SS_SINGLETON_VERTICAL `&3 / &2`]);;

(* Lean: southwest_west *)
let C975SS_SOUTHWEST_WEST = prove
 (c975ic_stmt [] (c975ic_own 256 `&3 / &2` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975IC_APPLY_TAC C981CP_POINT (c975ss_pullsw (c975ss_pully (c975ic_pullx (c975ic_owner 256))))
   [C975SS_SW_F4; C975SS_SW_G3; C975SS_SW_MARKER]
   [512, C975SS_SE_MARKER; 34816, C975SS_NW_MARKER;
    1, c975ss_bar C975SS_SINGLETON_HORIZONTAL `&8 / &5`;
    1, c975ss_bar C975SS_SINGLETON_HORIZONTAL `&3 / &2`]);;

(* Lean: southeast_g8_point *)
let C975SS_SOUTHEAST_G8_POINT = prove
 (c975ic_stmt [] (c975ic_own 512 `&3` `&8 / &5`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C975IC_COMPULSORY_TAC THEN
  REWRITE_TAC C975IC_AUXPTS THEN
  ASM_CASES_TAC (c975ic_mem 18 512) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (c975ic_mem 16 512) ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME) [mk_disj(c975ic_mem 16 512, c975ic_mem 18 512); mk_neg (c975ic_mem 18 512)] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_conj(c975ic_own 512 `&2` `&3 / &2`, c975ic_own 512 `&17 / &8` `&59 / &40`))
    (ASSUME_TAC o CONJUNCT1) THENL
   [C975IC_APPLY_TAC OCEP_POINTS_ORIGINAL (c975ic_owner 512)
     [C975SS_SE_MARKER; C975SS_SE_F8] [1024, C975SS_NE_MARKER; 16384, C975SS_RIGHT_MARKER];
    ALL_TAC] THEN
  MP_TAC (SPEC_ALL (oo_apart C975D_F 256 512)) THEN ASM_REWRITE_TAC[ldisj] THEN
  DISCH_THEN (MP_TAC o SPECL [`&2`; `&3 / &2`]) THEN ASM_SIMP_TAC[C975SS_SOUTHWEST_SOUTH]);;

(* Lean: southeast_g8 *)
let C975SS_SOUTHEAST_G8 = prove
 (c975ic_stmt [] (c975ic_mem 18 512),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM (oo_aux_point 18)] THEN
  ASM_SIMP_TAC[C975SS_SOUTHEAST_G8_POINT]);;

let C975SS_OFF = c975ss_seed_point 1 (`&187 / &100`, `&19 / &25`);;

(* Lean: bottom_reach *)
let C975SS_BOTTOM_REACH = prove
 (c975ic_stmt [] (mk_conj(c975ic_own 8192 `&14 / &5` `&1`,
    mk_forall(`x:real`, mk_imp(`&113 / &50 <= x`, mk_imp(`x <= &14 / &5`, c975ic_own 8192 `x:real` `&1`))))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  SUBGOAL_THEN (vsubst (zip (c975ic_owner 8192) [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`])
                  (rand (snd (strip_forall (concl C1089CB_REACH)))))
    (fun th -> ACCEPT_TAC (CONJUNCT2 th)) THEN
  C975IC_APPLY_TAC C1089CB_REACH (c975ic_owner 8192)
   [C975SS_BOTTOM_MARKER; C975SS_BOTTOM_F6; C975SS_BOTTOM_G5]
   [1, C975SS_H2; 1, C975SS_OFF; 512, C975SS_SE_MARKER]);;

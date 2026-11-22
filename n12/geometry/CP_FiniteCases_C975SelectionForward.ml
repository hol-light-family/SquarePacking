(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975SelectionForward.lean         *)
(* (namespace N12Compact.FiniteCases.C975Selection; Lean header: "Source     *)
(* only, uncompiled").  The C1090 elbow reduction forces NE F7 in C975.      *)
(* owner p m is the 5-tuple (ooc .. m) .. l; auxiliaries p m is ooaux .. m.  *)
(* Fields of selection_input / fixed: the C975SS_ / C975SEL_ theorems;       *)
(* OutwardBarPoint.point_original: OCOBP_POINT_ORIGINAL; ElbowPoint.         *)
(* points_original: OCEP_POINTS_ORIGINAL; CrossedElbow.impossible_original:  *)
(* OCCE_IMPOSSIBLE_ORIGINAL; C975IncomingPair.incoming_forces_top_seven:     *)
(* C975IP_INCOMING_FORCES_TOP_SEVEN.  The structure Cuts is c975sf_cuts.     *)
(* Tag C975SF_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975Selection.ml";;
needs "n12/geometry/CP_FiniteCases_C975IncomingPair.ml";;
needs "n12/geometry/CP_OtherCases_CrossedElbow.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;

let C975SF_APPLY_TAC th tp ths fors =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
                       REAL_RAT_REDUCE_CONV) (SPECL tp th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  (if concl th' = `false` then ALL_TAC else ALL_TAC) THEN
  (if rand (concl th') = `false`
   then SUBGOAL_THEN (lhand (concl th')) (fun h -> ACCEPT_TAC (MP th' h))
   else MATCH_MP_TAC th') THEN
  REPEAT CONJ_TAC THEN
  FIRST [C975IC_SIDE_TAC ths fors;
         X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
         FIRST (map (fun (n, th) -> C975IC_FOREIGN_TAC n th) fors)];;

let C975SF_B14 = prove
 (c975ic_stmt [] (c975ic_own 8192 `&14 / &5` `&1`),
  REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL C975SS_BOTTOM_REACH) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Lean: southeast_outward_sharp *)
let C975SF_SOUTHEAST_OUTWARD_SHARP = prove
 (c975ic_stmt [mk_neg (c975ic_own 512 `&113 / &50` `&2`)] (c975ic_own 512 `&101 / &40` `&17 / &8`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975SF_APPLY_TAC OCOBP_POINT_ORIGINAL (c975ss_pully (c975ic_owner 512))
   [C975SS_SE_MARKER; C975SS_SE_F8; C975SS_SOUTHEAST_G8_POINT]
   [16384, C975SS_RIGHT_MARKER; 12, C975SS_SE_CORNER; 12, C975SS_SE_CORNER_RIGHT;
    8192, C975SEL_BOTTOM_BAR]);;

(* Lean: northeast_elbow_points *)
let C975SF_NORTHEAST_ELBOW_POINTS = prove
 (c975ic_stmt [c975ic_own 1024 `&2` `&113 / &50`; mk_neg (c975ic_own 1024 `&12 / &5` `&3`)]
   (mk_conj(c975ic_own 1024 `&5 / &2` `&2`, c975ic_own 1024 `&101 / &40` `&17 / &8`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975SF_APPLY_TAC OCEP_POINTS_ORIGINAL (c975ss_pullsw (c975ic_pullx (c975ic_owner 1024)))
   [C975SS_NE_MARKER; C975SEL_NORTHEAST_SELECTION]
   [34816, C975SS_NW_MARKER; 34816, C975SS_TOP_MARKER]);;

(* Lean: northeast_f7_point *)
let C975SF_NORTHEAST_F7_POINT = prove
 (c975ic_stmt [] (c975ic_own 1024 `&12 / &5` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (c975ic_own 1024 `&12 / &5` `&3`) THEN ASM_REWRITE_TAC[] THEN
  C975IC_COMPULSORY_TAC THEN
  SUBGOAL_THEN (c975ic_own 1024 `&2` `&113 / &50`) ASSUME_TAC THENL
   [MP_TAC (ASSUME (mk_disj(c975ic_mem 5 1024, c975ic_mem 7 1024))) THEN
    UNDISCH_TAC (mk_neg (c975ic_own 1024 `&12 / &5` `&3`)) THEN
    REWRITE_TAC C975IC_AUXPTS THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  MP_TAC (SPEC_ALL C975SF_NORTHEAST_ELBOW_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC (c975ic_own 512 `&113 / &50` `&2`) THENL
   [C975SF_APPLY_TAC OCCE_IMPOSSIBLE_ORIGINAL (c975ic_owner 512 @ [`&4 / &5`])
     [C975SS_SE_MARKER; C975SS_SE_F8]
     [1024, ASSUME (c975ic_own 1024 `&5 / &2` `&2`); 256, C975SS_SOUTHWEST_SOUTH; 8192, C975SF_B14];
    MP_TAC (SPEC_ALL C975SF_SOUTHEAST_OUTWARD_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC (SPEC_ALL (oo_apart C975D_F 512 1024)) THEN ASM_REWRITE_TAC[ldisj] THEN
    DISCH_THEN (MP_TAC o SPECL [`&101 / &40`; `&17 / &8`]) THEN ASM_REWRITE_TAC[]]);;

(* Lean: northeast_f7 *)
let C975SF_NORTHEAST_F7 = prove
 (c975ic_stmt [] (c975ic_mem 7 1024),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM (oo_aux_point 7)] THEN
  ASM_SIMP_TAC[C975SF_NORTHEAST_F7_POINT]);;

(* Lean: not_northeast_incoming *)
let C975SF_NOT_NORTHEAST_INCOMING = prove
 (c975ic_stmt [] (mk_neg (mk_conj(c975ic_mem 5 1024, c975ic_mem 16 1024))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC_ALL C975SEL_NOT_TOP_G7) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C975IP_INCOMING_FORCES_TOP_SEVEN THEN ASM_REWRITE_TAC[]);;

(* Lean: Cuts.topG4 source, C975Entrance.compulsory .top *)
let C975SF_TOP_G4 = prove
 (c975ic_stmt [] (c975ic_mem 14 34816),
  REPEAT STRIP_TAC THEN MP_TAC (SPEC_ALL C975E_COMPULSORY) THEN
  ASM_REWRITE_TAC[c975e_compulsory] THEN SIMP_TAC[]);;

let C975SF_CUT_THMS =
  [C975SS_SOUTHWEST_SOUTH; C975SS_SOUTHWEST_WEST; C975SS_SOUTHEAST_G8; C975SEL_NORTHEAST_G7;
   C975SF_NORTHEAST_F7; C975IC_TOP_LEFT; C975SF_TOP_G4; C975SEL_TOP_G_EXACT;
   C975IC_NOT_TOP_INWARD; C975SEL_NOT_TOP_F7; C975IC_NOT_TOP_ELBOW; C975SF_NOT_NORTHEAST_INCOMING];;

(* Lean: Cuts (structure) *)
let c975sf_cuts =
  let body = list_mk_conj (map (fun th -> rand (snd (strip_forall (concl th)))) C975SF_CUT_THMS) in
  new_definition (mk_eq(list_mk_comb(`c975sf_cuts:(num->real)->(num->real)->(num->real)->(num->real)->real->bool`,
                                      C975IC_V5), body));;

(* Lean: cuts *)
let C975SF_CUTS = prove
 (c975ic_stmt [] `c975sf_cuts c1 c2 a b l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[c975sf_cuts] THEN
  REPEAT CONJ_TAC THEN FIRST (map (fun th -> MATCH_MP_TAC th THEN ASM_REWRITE_TAC[] THEN NO_TAC)
                                  C975SF_CUT_THMS));;

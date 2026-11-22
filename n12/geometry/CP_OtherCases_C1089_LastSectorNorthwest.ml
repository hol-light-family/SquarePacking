(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastSectorNorthwest.lean      *)
(* (namespace N12Compact.Completion.OtherCases.C1089.LastSectorNorthwest).  *)
(* The actual northwest ordinary pair of C1089-LAST-SECTOR-REDUCTION §4--5.  *)
(* q : Fin 12 -> OpenSquare as in LastSectorNorthwestInput (qc qs qu qv qa, *)
(* unit normals as the hypothesis !i. i < 12 ==> qc i*qc i+qs i*qs i = &1). *)
(* Charts of Q = (c, s, u, v, a):                                           *)
(*   pullY (pullX Q): C1089LSNI_CHART, inside x y <=> Q inside (4-x) (4-y); *)
(*   pullSwap Q = (s, c, u, --v - a, a): LINSIDE_PULLSW (swap x y);         *)
(*   pullX Q: LINSIDE_PULLX, inside x y <=> Q inside (4 - x) y.             *)
(* CommonCases.InwardPoint.point_original: CCIP_POINT_ORIGINAL;             *)
(* InnerCornerObstruction.inward_corner_excluded_original:                  *)
(* OCICOI_INWARD_CORNER_EXCLUDED_ORIGINAL; .corner_excluded_original:       *)
(* OCICOM_CORNER_EXCLUDED_ORIGINAL; ElbowPoint.points_original:             *)
(* OCEP_POINTS_ORIGINAL; CrossedElbow.impossible_original:                  *)
(* OCCE_IMPOSSIBLE_ORIGINAL; C1092MixedSpan.impossible: C1092MS_IMPOSSIBLE; *)
(* ShortDuplicatePoints.inward_original: OCSDP_INWARD_ORIGINAL.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastSectorNorthwestInput.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_OtherCases_ShortDuplicatePoints.ml";;
needs "n12/geometry/CP_OtherCases_InnerCornerObstruction_Inward.ml";;
needs "n12/geometry/CP_OtherCases_InnerCornerObstruction_Main.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_OtherCases_CrossedElbow.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;

(* unfold the input into separate assumptions (disjunctions kept whole), plus
   the unit normal and side of squares 4 and 7 *)
let C1089LSNW_SETUP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[c1089lsni_input] o check (fun th ->
    fst(strip_comb(concl th)) = `c1089lsni_input`)) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `qc 4 * qc 4 + qs 4 * qs 4 = &1 /\ qc 7 * qc 7 + qs 7 * qs 7 = &1 /\
                &1 < qa 4 /\ &1 < qa 7` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM(fun th ->
      MATCH_MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC);
    ALL_TAC];;

(* side conditions of a chart application *)
let C1089LSNW_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
           FIRST_ASSUM ACCEPT_TAC;
         ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
         CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
         FIRST (map (fun j -> C1089LSNI_FOREIGN_TAC () j THEN NO_TAC)
           [`0`; `4`; `5`; `6`; `7`; `8`; `11`]);
         RASM_ARITH_TAC];;

let C1089LSNW_APPLY_TAC th tuple chart =
  let th1 = CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (REWRITE_RULE[chart; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] (SPECL tuple th)) in
  MP_TAC(if is_neg(concl th1) then NOT_ELIM th1 else th1) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089LSNW_SIDE_TAC; DISCH_TAC] THEN
  TRY(FIRST_ASSUM CONTR_TAC);;

let C1089LSNW_PXY7 = [`--(qc 7):real`; `--(qs 7):real`; `qu 7 - &4 * qc 7 - &4 * qs 7`;
                      `qv 7 + &4 * qs 7 - &4 * qc 7`; `qa 7:real`];;
let C1089LSNW_SW7 = [`qs 7:real`; `qc 7:real`; `qu 7:real`; `--(qv 7) - qa 7`; `qa 7:real`];;
let C1089LSNW_PX7 = [`--(qc 7):real`; `qs 7:real`; `qu 7 - &4 * qc 7`;
                     `--(qv 7) - qa 7 - &4 * qs 7`; `qa 7:real`];;
let C1089LSNW_PX4 = [`--(qc 4):real`; `qs 4:real`; `qu 4 - &4 * qc 4`;
                     `--(qv 4) - qa 4 - &4 * qs 4`; `qa 4:real`];;
let C1089LSNW_Q4 = [`qc 4:real`; `qs 4:real`; `qu 4:real`; `qv 4:real`; `qa 4:real`];;

let C1089LSNW_OUTWARD_TAC =
  MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                `qa:num->real`] C1089LSNI_OUTWARD_POINTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC;;

(* Lean: northwest_f3 *)
let C1089LSNW_NORTHWEST_F3 = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lsni_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3)`,
  C1089LSNW_SETUP_TAC THEN
  ASM_CASES_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                  `qa:num->real`] C1089LSNI_F_ALTERNATIVES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2)` THENL
   [C1089LSNW_APPLY_TAC CCIP_POINT_ORIGINAL C1089LSNW_PXY7 C1089LSNI_CHART THEN
    SUBGOAL_THEN `~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2)`
      ASSUME_TAC THENL [C1089LSNW_SIDE_TAC; ALL_TAC] THEN
    C1089LSNW_APPLY_TAC OCICOI_INWARD_CORNER_EXCLUDED_ORIGINAL
      (C1089LSNW_Q4 @ [`&27 / &50`; `&101 / &100`]) TRUTH THEN
    C1089LSNW_OUTWARD_TAC THEN
    MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                  `qa:num->real`; `4`; `7`; `&77 / &50`; `&201 / &100`]
      C1089LSNI_FOREIGN) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                  `qa:num->real`] C1089LSNI_G_ALTERNATIVES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  C1089LSNW_APPLY_TAC OCEP_POINTS_ORIGINAL C1089LSNW_SW7 LINSIDE_PULLSW THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  SUBGOAL_THEN `linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&6 / &5) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC C1089LSNI_SINGLETON_BAR THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2)`
    ASSUME_TAC THENL
   [DISCH_TAC THEN
    C1089LSNW_APPLY_TAC OCCE_IMPOSSIBLE_ORIGINAL (C1089LSNW_PX4 @ [`&4 / &5`])
      LINSIDE_PULLX;
    ALL_TAC] THEN
  C1089LSNW_APPLY_TAC OCICOM_CORNER_EXCLUDED_ORIGINAL C1089LSNW_Q4 TRUTH THEN
  C1089LSNW_OUTWARD_TAC THEN
  MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                `qa:num->real`; `4`; `7`; `&59 / &40`; `&17 / &8`]
    C1089LSNI_FOREIGN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: northwest_g4 *)
let C1089LSNW_NORTHWEST_G4 = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lsni_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)`,
  C1089LSNW_SETUP_TAC THEN
  MP_TAC(SPEC_ALL C1089LSNW_NORTHWEST_F3) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2)`
    ASSUME_TAC THENL
   [MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                  `qa:num->real`] C1089LSNI_G_ALTERNATIVES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)`
    ASSUME_TAC THENL
   [ASM_CASES_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)` THEN
    ASM_REWRITE_TAC[] THEN
    C1089LSNW_APPLY_TAC C1092MS_IMPOSSIBLE C1089LSNW_SW7 LINSIDE_PULLSW;
    ALL_TAC] THEN
  C1089LSNW_APPLY_TAC OCSDP_INWARD_ORIGINAL C1089LSNW_PX7 LINSIDE_PULLX THEN
  SUBGOAL_THEN `~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2)`
    ASSUME_TAC THENL [C1089LSNW_SIDE_TAC; ALL_TAC] THEN
  C1089LSNW_APPLY_TAC OCICOI_INWARD_CORNER_EXCLUDED_ORIGINAL
    (C1089LSNW_Q4 @ [`&1 / &2`; `&26 / &25`]) TRUTH THEN
  C1089LSNW_OUTWARD_TAC THEN
  MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                `qa:num->real`; `4`; `7`; `&3 / &2`; `&51 / &25`]
    C1089LSNI_FOREIGN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: ordinary_pair *)
let C1089LSNW_ORDINARY_PAIR = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lsni_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) /\
         linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)`,
  SIMP_TAC[C1089LSNW_NORTHWEST_F3; C1089LSNW_NORTHWEST_G4]);;

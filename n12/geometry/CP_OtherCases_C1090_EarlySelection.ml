(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/EarlySelection.lean          *)
(* (namespace N12Compact.Completion.OtherCases.C1090.Early; Lean header:     *)
(* "Source only, not compiled").  C1090-SIMPLIFIED-PROOF sections 4--6.      *)
(* q : Fin 12 -> OpenSquare as in EarlyGeometry.ml: q i = (qc i, qs i, qu i,  *)
(* qv i, qa i), unit normals as the hypothesis !i. i < 12 ==> qc i * qc i +   *)
(* qs i * qs i = &1; Input q = c1090eg_input; NESelectionOwners.Data =       *)
(* c1090neso_data; PointTable q = c1090es_pointTable (Input plus the fields).*)
(* C1092MixedSpan.impossible = C1092MS_IMPOSSIBLE (at the half turn         *)
(* pullY (pullX (q 7))), C1089.WallOrigins = OC1089WO_*,                     *)
(* C981CompletionUpperPoint.point = C981UP_POINT, inside_segment on vertical *)
(* / horizontal segments = OO_VERTICAL_SEGMENT / OO_HORIZONTAL_SEGMENT.      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1090_EarlyGeometry.ml";;
needs "n12/geometry/CP_OtherCases_C1090_NESelectionOwners.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallOrigins.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/CP_C981_UpperPoint.ml";;

let C1090ES_LDISJ = prove
 (`forall qc qs qu qv qa i j. c1090eg_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (qc i) (qs i) (qu i) (qv i) (qa i) (qc j) (qs j) (qu j) (qv j) (qa j)`,
  REWRITE_TAC[c1090eg_input; ldisj] THEN MESON_TAC[]);;
let C1090ES_SAME = prove
 (`forall qc qs qu qv qa i j. c1090eg_input qc qs qu qv qa /\ i < 12 /\ j < 12 ==> qa i = qa j`,
  REWRITE_TAC[c1090eg_input] THEN MESON_TAC[]);;

let C1090ES_VARS = [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

(* side conditions of an applied lemma: assumption, ldisj / same side from Input *)
let C1090ES_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC C1090ES_LDISJ THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         MATCH_MP_TAC (SPECL C1090ES_VARS C1090ES_SAME) THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC];;
let C1090ES_APPLY_TAC th =
  MATCH_MP_TAC th THEN REPEAT CONJ_TAC THEN C1090ES_SIDE_TAC;;
let C1090ES_START_TAC is =
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY C1090EG_SQUARE_TAC is THEN C1090EG_UNFOLD_TAC;;
let C1090ES_NOT_TAC tm js =
  SUBGOAL_THEN (mk_neg tm) ASSUME_TAC THENL [C1090EG_FOREIGN_TAC js; ALL_TAC];;
let C1090ES_USE thl = MAP_EVERY (fun th ->
  MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC) thl;;

(* Lean: selection_input *)
let C1090ES_SELECTION_INPUT = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa ==> c1090neso_data qc qs qu qv qa`,
  C1090ES_START_TAC [] THEN
  C1090ES_USE [C1090EG_SOUTHEAST_G8; C1090EG_BOTTOM_ADVANCE] THEN
  C1090ES_NOT_TAC `linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50)` [10] THEN
  C1090ES_NOT_TAC `linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&12 / &5)` [10] THEN
  REWRITE_TAC[c1090neso_data] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50) \/ linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3) \/ linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50)`;
      `~linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50)`] THEN CONV_TAC TAUT;
    MAP_EVERY (MP_TAC o ASSUME)
     [`linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&2) \/ linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3) \/ linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&12 / &5)`;
      `~linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&12 / &5)`] THEN CONV_TAC TAUT]);;

(* Lean: northeast_selection *)
let C1090ES_NORTHEAST_SELECTION = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3) /\
         (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&2) ==> linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1090NESO_SELECTION THEN
  ASM_SIMP_TAC[C1090ES_SELECTION_INPUT]);;

(* Lean: top_pair *)
let C1090ES_TOP_PAIR = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&8 / &5) (&3) /\ linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)`,
  C1090ES_START_TAC [] THEN C1090ES_USE [C1090ES_NORTHEAST_SELECTION] THEN
  C1090ES_NOT_TAC `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&113 / &50) (&3)` [6] THEN
  MAP_EVERY (MP_TAC o ASSUME)
   [`linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&113 / &50) (&3) \/ (linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&8 / &5) (&3) /\ linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3))`;
    `~linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&113 / &50) (&3)`] THEN CONV_TAC TAUT);;

(* Lean: northwest_pair *)
let C1090ES_NORTHWEST_PAIR = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50) /\ linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5)`,
  C1090ES_START_TAC [7] THEN C1090ES_USE [C1090ES_TOP_PAIR] THEN
  C1090ES_NOT_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2)` [4] THEN
  C1090ES_NOT_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)` [11] THEN
  C1090ES_NOT_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3)` [11] THEN
  SUBGOAL_THEN `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5)` ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5) \/ linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) \/ linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)`;
      `~linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2)`; `~linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)`] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50)` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)` ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME)
     [`linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50) \/ linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) \/ linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)`;
      `~linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50)`; `~linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3)`] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  MP_TAC (SPECL (c1090eg_pully (c1090eg_pullx (c1090eg_q 7))) C1092MS_IMPOSSIBLE) THEN
  REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: top_advance *)
let C1090ES_TOP_ADVANCE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa ==> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&36 / &25) (&3)`,
  C1090ES_START_TAC [11] THEN C1090ES_USE [C1090ES_TOP_PAIR; C1090ES_NORTHEAST_SELECTION] THEN
  C1090ES_APPLY_TAC
    (SPECL (c1090eg_q 11 @ c1090eg_q 6 @ c1090eg_q 7) OC1089WO_TOP_LEFT_ADVANCE));;

(* Lean: top_origin *)
let C1090ES_TOP_ORIGIN = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa ==> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&3)`,
  C1090ES_START_TAC [7; 11; 3] THEN C1090ES_USE [C1090ES_TOP_PAIR; C1090ES_NORTHWEST_PAIR] THEN
  C1090ES_APPLY_TAC
    (SPECL (c1090eg_q 7 @ c1090eg_q 4 @ c1090eg_q 8 @ c1090eg_q 11 @ c1090eg_q 3)
       OC1089WO_TOP_ORIGIN_FROM_NORTHWEST));;

(* Lean: top_bar *)
let C1090ES_TOP_BAR = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa
     ==> forall x. &36 / &25 <= x ==> x <= &2 ==> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) x (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090ES_USE [C1090ES_TOP_ADVANCE; C1090ES_TOP_ORIGIN] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&36 / &25`; `&2`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: top_f5_excluded *)
let C1090ES_TOP_F5_EXCLUDED = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa ==> ~linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&113 / &50)`,
  C1090ES_START_TAC [6] THEN C1090ES_USE [C1090ES_NORTHEAST_SELECTION; C1090EG_RIGHT_ADVANCE] THEN
  DISCH_TAC THEN
  MAP_EVERY (fun y -> SUBGOAL_THEN (subst [y, `y:real`] `linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) y`) ASSUME_TAC THENL
     [MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&113 / &50`; `&1543 / &500`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC])
    [`&12 / &5`; `&3`; `&131 / &50`] THEN
  C1090ES_NOT_TAC `linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&131 / &50)` [11] THEN
  SUBGOAL_THEN `linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&131 / &50)` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC C981UP_POINT THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  C1090EG_FOREIGN_TAC [11; 10; 2]);;

(* Lean: PointTable (structure) *)
let c1090es_pointTable = new_definition
 `c1090es_pointTable (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    c1090eg_input qc qs qu qv qa /\
    (forall y. &5 / &4 <= y ==> y <= &7 / &4 ==> linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) y) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&14 / &5) (&1) /\
    (forall x. &113 / &50 <= x ==> x <= &14 / &5 ==> linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) x (&1)) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&64 / &25) /\
    (forall y. &113 / &50 <= y ==> y <= &64 / &25 ==> linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) y) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&3 / &2) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&3 / &2) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&8 / &5) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3) /\
    (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&2) ==> linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3)) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&8 / &5) (&3) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&36 / &25) (&3) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&3) /\
    (forall x. &36 / &25 <= x ==> x <= &2 ==> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) x (&3)) /\
    ~linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&113 / &50)`;;

(* Lean: point_table *)
let C1090ES_POINT_TABLE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090eg_input qc qs qu qv qa ==> c1090es_pointTable qc qs qu qv qa`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c1090es_pointTable] THEN ASM_REWRITE_TAC[] THEN
  C1090ES_USE [C1090EG_LEFT_BAR; C1090EG_BOTTOM_ADVANCE; C1090EG_RIGHT_ADVANCE;
               C1090EG_SOUTHWEST_SOUTH; C1090EG_SOUTHWEST_WEST; C1090EG_SOUTHEAST_G8;
               C1090ES_NORTHEAST_SELECTION; C1090ES_NORTHWEST_PAIR; C1090ES_TOP_PAIR;
               C1090ES_TOP_ADVANCE; C1090ES_TOP_ORIGIN; C1090ES_TOP_BAR; C1090ES_TOP_F5_EXCLUDED] THEN
  ASM_SIMP_TAC[] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C1090EG_RIGHT_BAR THEN ASM_REWRITE_TAC[]);;

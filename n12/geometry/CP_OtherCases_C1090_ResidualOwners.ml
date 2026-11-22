(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1090/ResidualOwners.lean           *)
(* (namespace N12Compact.Completion.OtherCases.C1090.Residual).              *)
(* Actual-owner producers for the residual ending (C1089-REVERSE-CYCLIC-     *)
(* ENDING sections 5--6).  q : Fin 12 -> OpenSquare is written as five       *)
(* coordinate functions qc qs qu qv qa : num -> real (i < 12); the OpenSquare *)
(* unit normals are the explicit hypothesis                                  *)
(*   !i. i < 12 ==> qc i * qc i + qs i * qs i = &1.                          *)
(* Input is c1090ro_input (fields in Lean order).  q.translated x y is the   *)
(* 5-tuple (c, s, u - (c * x + s * y), v - (--s * x + c * y), a)             *)
(* (C1090RO_INSIDE_TRANSLATED = S12.inside_translated_iff); pullX as in       *)
(* p2_base (LINSIDE_PULLX).  Used: C1089 WallOrigins (OC1089WO_), F4Point-   *)
(* Transfers (OCF4PT_), UpperBarPoint (OCUBP_), ResidualCentralPoints        *)
(* (C1090RCP_), WallProfile.boundary_origin (OCWPBO_), SouthwestSupport-     *)
(* Point (OCSWSPM_), OrdinaryLeftTop Input / frame / ShallowTop.TopInput     *)
(* (ocolti_input, OLTM_FRAME, oltstsu_top).  Tag C1090RO_ / c1090ro_.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/CP_OtherCases_C1090_ResidualCentralPoints.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallOrigins.ml";;
needs "n12/geometry/CP_OtherCases_F4PointTransfers.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_TopOnlyLeftPoint.ml";;
needs "n12/geometry/CP_OtherCases_SouthwestSupportPoint_Main.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryLeftTop_ShallowTopPair.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

(* Lean: Input (structure) *)
let c1090ro_input = new_definition
 `c1090ro_input (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
    (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&457 / &500) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&1) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&3) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&1543 / &500) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&3) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&87 / &50) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&3 / &2) (&2) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&3 / &2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&8 / &5) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&87 / &50) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&8 / &5) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&457 / &500) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&12 / &5) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&113 / &50) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&14 / &5) (&1) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&113 / &50) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&64 / &25) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&8 / &5) (&3) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3)`;;

(* Lean: S12.inside_translated_iff (source/S12/Diagonal.lean) *)
let C1090RO_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: S12.inside_segment, with the segment parameter left implicit *)
let C1090RO_SEGMENT_POINT = prove
 (`forall c s u v a x0 y0 x1 y1 x y t.
     linside c s u v a x0 y0 /\ linside c s u v a x1 y1 /\ &0 <= t /\ t <= &1 /\
     x = (&1 - t) * x0 + t * x1 /\ y = (&1 - t) * y0 + t * y1
     ==> linside c s u v a x y`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CES_INSIDE_SEGMENT THEN
  ASM_REWRITE_TAC[]);;

let C1090RO_APART_AT = prove
 (`forall qc qs qu qv qa i j x y.
     c1090ro_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
           linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)`,
  REWRITE_TAC[c1090ro_input] THEN MESON_TAC[]);;

(* foreign: a point of q j is not in q i *)
let C1090RO_FOREIGN = prove
 (`forall qc qs qu qv qa i x y j.
     c1090ro_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (qc j) (qs j) (qu j) (qv j) (qa j) x y
     ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REWRITE_TAC[c1090ro_input] THEN MESON_TAC[]);;

let C1090RO_INPUT_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1090ro_input] o
    check (fun th -> can (term_match [] `c1090ro_input qc qs qu qv qa`) (concl th)));;

(* a goal P k from an assumption !i. i < 12 ==> P i (or the two-index forms) *)
let C1090RO_BY_FORALL_TAC =
  FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC);;

let C1090RO_FOREIGN_TAC j =
  MATCH_MP_TAC C1090RO_FOREIGN THEN EXISTS_TAC j THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;;

(* side conditions of the geometric lemmas *)
let C1090RO_SIDE_TAC =
  FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    C1090RO_BY_FORALL_TAC;
    MATCH_MP_TAC(REAL_ARITH `&1 < x ==> &0 < x`) THEN C1090RO_BY_FORALL_TAC;
    REWRITE_TAC[ldisj] THEN C1090RO_BY_FORALL_TAC;
    MATCH_MP_TAC C1090RO_APART_AT THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC];;

let C1090RO_UNIT_HYP =
  `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1`;;

(* Lean: bottom_bar *)
let C1090RO_BOTTOM_BAR = prove
 (`forall qc qs qu qv qa x. c1090ro_input qc qs qu qv qa /\ &113 / &50 <= x /\ x <= &14 / &5
     ==> linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090RO_INPUT_TAC THEN
  MATCH_MP_TAC C1090RO_SEGMENT_POINT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&1`; `&14 / &5`; `&1`; `(&50 / &27) * (x - &113 / &50)`] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: right_bar *)
let C1090RO_RIGHT_BAR = prove
 (`forall qc qs qu qv qa y. c1090ro_input qc qs qu qv qa /\ &113 / &50 <= y /\ y <= &64 / &25
     ==> linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090RO_INPUT_TAC THEN
  MATCH_MP_TAC C1090RO_SEGMENT_POINT THEN
  MAP_EVERY EXISTS_TAC [`&3`; `&113 / &50`; `&3`; `&64 / &25`; `(&10 / &3) * (y - &113 / &50)`] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: top_advance *)
let C1090RO_TOP_ADVANCE = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa
     ==> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&36 / &25) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090RO_INPUT_TAC THEN
  MATCH_MP_TAC OC1089WO_TOP_LEFT_ADVANCE THEN
  MAP_EVERY EXISTS_TAC [`qc 6:real`; `qs 6:real`; `qu 6:real`; `qv 6:real`; `qa 6:real`;
                        `qc 7:real`; `qs 7:real`; `qu 7:real`; `qv 7:real`; `qa 7:real`] THEN
  REPEAT CONJ_TAC THEN C1090RO_SIDE_TAC);;

(* Lean: top_origin *)
let C1090RO_TOP_ORIGIN = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa
     ==> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090RO_INPUT_TAC THEN
  MP_TAC(SPECL (map (fun i -> map (fun f -> mk_comb(f, mk_small_numeral i))
                  [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`])
                  [7; 4; 8; 11; 3] |> List.concat) OC1089WO_TOP_ORIGIN_FROM_NORTHWEST) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THEN C1090RO_SIDE_TAC);;

(* Lean: southeast_east *)
let C1090RO_SOUTHEAST_EAST = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa
     ==> linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&5 / &2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`;
                `&5 / &2`] C1090RO_BOTTOM_BAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  C1090RO_INPUT_TAC THEN MATCH_MP_TAC OCF4PT_HORIZONTAL_ORIGINAL THEN
  REPEAT CONJ_TAC THENL
   [C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC;
    C1090RO_SIDE_TAC; C1090RO_FOREIGN_TAC `4`; C1090RO_FOREIGN_TAC `9`]);;

(* Lean: northeast_outer_sharp *)
let C1090RO_NORTHEAST_OUTER_SHARP = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa /\
     ~linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50)
     ==> linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&101 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_TOP_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN MATCH_MP_TAC OCUBP_POINT_ORIGINAL THEN
  REPEAT CONJ_TAC THENL
   [C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC;
    C1090RO_SIDE_TAC; C1090RO_FOREIGN_TAC `11`; C1090RO_FOREIGN_TAC `2`;
    X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC C1090RO_FOREIGN THEN EXISTS_TAC `10` THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C1090RO_RIGHT_BAR THEN ASM_REWRITE_TAC[]]);;

(* Lean: northeast_mixed_sharp *)
let C1090RO_NORTHEAST_MIXED_SHARP = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa /\
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50)
     ==> linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&121 / &50) (&54 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_TOP_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  MP_TAC(SPECL [`qc 6:real`; `qs 6:real`; `qu 6 - (qc 6 * &2 + qs 6 * &2)`;
                `qv 6 - (--qs 6 * &2 + qc 6 * &2)`; `qa 6:real`] C1090RCP_MIXED_POINT) THEN
  REWRITE_TAC[C1090RO_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC;
    C1090RO_SIDE_TAC; C1090RO_FOREIGN_TAC `7`; C1090RO_FOREIGN_TAC `11`;
    C1090RO_FOREIGN_TAC `2`; C1090RO_FOREIGN_TAC `10`]);;

(* Lean: southeast_lower  (the local `transfer` is C1090RO_SOUTHEAST_TRANSFER) *)
let C1090RO_SOUTHEAST_TRANSFER = prove
 (`forall qc qs qu qv qa a b. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa /\ c1090rcp_parameters a b /\
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2 + a) (&2 + b)
     ==> linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1090RO_INPUT_TAC THEN
  MP_TAC(SPECL [`qc 5:real`; `qs 5:real`; `qu 5 - (qc 5 * &2 + qs 5 * &2)`;
                `qv 5 - (--qs 5 * &2 + qc 5 * &2)`; `qa 5:real`; `a:real`; `b:real`]
    C1090RCP_SOUTHEAST_POINT) THEN
  REWRITE_TAC[C1090RO_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC;
    C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_FOREIGN_TAC `4`; C1090RO_FOREIGN_TAC `6`]);;

let C1090RO_SOUTHEAST_LOWER = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa
     ==> linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&3 / &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50)` THENL
   [MATCH_MP_TAC C1090RO_SOUTHEAST_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`&21 / &50`; `&4 / &25`] THEN
    ASM_REWRITE_TAC[c1090rcp_parameters] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC C1090RO_NORTHEAST_MIXED_SHARP THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C1090RO_SOUTHEAST_TRANSFER THEN
    MAP_EVERY EXISTS_TAC [`&21 / &40`; `&1 / &8`] THEN
    ASM_REWRITE_TAC[c1090rcp_parameters] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC C1090RO_NORTHEAST_OUTER_SHARP THEN ASM_REWRITE_TAC[]]);;

(* Lean: bottom_origin *)
let C1090RO_BOTTOM_ORIGIN = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa
     ==> linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_SOUTHEAST_LOWER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  let px i = [mk_comb(`(--):real->real`, mk_comb(`qc:num->real`, i)); mk_comb(`qs:num->real`, i);
              subst [i, `k:num`] `qu (k:num) - &4 * qc k`;
              subst [i, `k:num`] `--qv (k:num) - qa k - &4 * qs k`; mk_comb(`qa:num->real`, i)] in
  MP_TAC(SPECL (px `9` @ px `1` @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[LINSIDE_PULLX; ldisj; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN
  FIRST
   [C1090RO_SIDE_TAC;
    C1090RO_FOREIGN_TAC `5`;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `lcont (qc 9) (qs 9) (qu 9) (qv 9) (qa 9)` MP_TAC THENL
     [C1090RO_BY_FORALL_TAC; REWRITE_TAC[lcont]] THEN
    DISCH_THEN(MP_TAC o SPECL [`&4 - x`; `y:real`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `lcont (qc 1) (qs 1) (qu 1) (qv 1) (qa 1)` MP_TAC THENL
     [C1090RO_BY_FORALL_TAC; REWRITE_TAC[lcont]] THEN
    DISCH_THEN(MP_TAC o SPECL [`&4 - x`; `y:real`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN MATCH_MP_TAC C1090RO_APART_AT THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV]);;

(* Lean: southwest_support *)
let C1090RO_SOUTHWEST_SUPPORT = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa
     ==> linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&127 / &100) (&49 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_BOTTOM_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  SUBGOAL_THEN `linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&3 / &2) (&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC C1090RO_SEGMENT_POINT THEN
    MAP_EVERY EXISTS_TAC [`&28 / &25`; `&1`; `&87 / &50`; `&1`; `&19 / &31`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OCSWSPM_POINT_OF_NEIGHBOURS THEN
  MAP_EVERY EXISTS_TAC [`qc 0:real`; `qs 0:real`; `qu 0:real`; `qv 0:real`; `qa 0:real`;
                        `qc 5:real`; `qs 5:real`; `qu 5:real`; `qv 5:real`; `qa 5:real`] THEN
  REPEAT CONJ_TAC THENL
   [C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC;
    C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC;
    C1090RO_FOREIGN_TAC `7`; C1090RO_FOREIGN_TAC `9`; C1090RO_FOREIGN_TAC `8`;
    C1090RO_FOREIGN_TAC `8`;
    C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC;
    C1090RO_SIDE_TAC; C1090RO_SIDE_TAC]);;

let c1090ro_t7 =
  [`qc 7:real`; `qs 7:real`; `qu 7 - (qc 7 * &1 + qs 7 * &2)`;
   `qv 7 - (--qs 7 * &1 + qc 7 * &2)`; `qa 7:real`];;

(* Lean: ordinary_input *)
let C1090RO_ORDINARY_INPUT = prove
 (mk_forall(`qc:num->real`, mk_forall(`qs:num->real`, mk_forall(`qu:num->real`,
   mk_forall(`qv:num->real`, mk_forall(`qa:num->real`,
   mk_imp(`(forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090ro_input qc qs qu qv qa`,
          list_mk_comb(`ocolti_input`, c1090ro_t7))))))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_SOUTHWEST_SUPPORT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_TOP_ADVANCE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  REWRITE_TAC[ocolti_input; C1090RO_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT CONJ_TAC THENL
   [C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC;
    C1090RO_FOREIGN_TAC `8`; C1090RO_FOREIGN_TAC `4`; C1090RO_FOREIGN_TAC `4`;
    C1090RO_FOREIGN_TAC `3`; C1090RO_FOREIGN_TAC `4`; C1090RO_FOREIGN_TAC `11`;
    C1090RO_FOREIGN_TAC `11`]);;

(* Lean: northwest_upper_points *)
let C1090RO_NORTHWEST_UPPER_POINTS = prove
 (`forall qc qs qu qv qa. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&32 / &25) (&3) /\
         linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&7 / &5) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_ORDINARY_INPUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  MP_TAC(SPECL c1090ro_t7 OLTM_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN C1090RO_SIDE_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `ar:real`] THEN
  STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1090RO_INSIDE_TRANSLATED]) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[th]) else NO_TAC) THEN
  RULE_ASSUM_TAC(CONV_RULE REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]);;

(* Lean: top_input *)
let C1090RO_TOP_INPUT = prove
 (`forall qc qs qu qv qa cW sW uW vW aW. (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1090ro_input qc qs qu qv qa /\
     (forall x y. linside cW sW uW vW aW x y <=> linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) x y)
     ==> oltstsu_top cW sW (uW - (cW * &1 + sW * &2)) (vW - (--sW * &1 + cW * &2)) aW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_TOP_ADVANCE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1090RO_TOP_ORIGIN) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1090RO_INPUT_TAC THEN
  ASM_REWRITE_TAC[oltstsu_top; C1090RO_INSIDE_TRANSLATED] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
   [C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_SIDE_TAC; C1090RO_FOREIGN_TAC `6`;
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `lcont (qc 11) (qs 11) (qu 11) (qv 11) (qa 11)` MP_TAC THENL
     [C1090RO_BY_FORALL_TAC; REWRITE_TAC[lcont]] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1 + x`; `&2 + y`]) THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC]);;

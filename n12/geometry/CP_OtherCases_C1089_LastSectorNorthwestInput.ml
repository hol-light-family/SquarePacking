(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastSectorNorthwestInput.lean *)
(* (namespace N12Compact.Completion.OtherCases.C1089.LastSectorNorthwest).  *)
(* Actual inputs and common outward consequences for sections 4--5 of       *)
(* C1089-LAST-SECTOR-REDUCTION.                                             *)
(* q : Fin 12 -> OpenSquare is written as five coordinate functions          *)
(*   qc qs qu qv qa : num -> real,  q i = (qc i, qs i, qu i, qv i, qa i),    *)
(* i < 12; the unit normals are the explicit hypothesis                     *)
(*   !i. i < 12 ==> qc i * qc i + qs i * qs i = &1.                         *)
(* pullY (pullX Q) of Q = (c, s, u, v, a) is the 5-tuple                     *)
(*   (--c, --s, u - &4 * c - &4 * s, v + &4 * s - &4 * c, a)  (chart:        *)
(* inside x y <=> Q inside (4 - x) (4 - y)).  S12.inside_segment:            *)
(* CES_INSIDE_SEGMENT; CommonCases.OutwardPoint.point_original:             *)
(* CCOP_POINT_ORIGINAL; ShortDuplicatePoints.outward_of_bar:                *)
(* OCSDP_OUTWARD_OF_BAR; OutwardBarPoint.point_original:                    *)
(* OCOBP_POINT_ORIGINAL.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;
needs "n12/geometry/CP_OtherCases_ShortDuplicatePoints.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarPoint.ml";;

(* Lean: Input (structure) *)
let c1089lsni_input = new_definition
 `c1089lsni_input (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&457 / &500) (&1) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&8 / &5) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&3 / &2) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)) /\
    (linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) \/
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&113 / &50) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&12 / &5) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500)`;;

(* Input.apart, as a foreign-point exclusion *)
let C1089LSNI_FOREIGN = prove
 (`forall qc qs qu qv qa i j x y.
     c1089lsni_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (qc j) (qs j) (qu j) (qv j) (qa j) x y
     ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REWRITE_TAC[c1089lsni_input] THEN MESON_TAC[]);;

let C1089LSNI_FOREIGN_TAC i j =
  MATCH_MP_TAC C1089LSNI_FOREIGN THEN EXISTS_TAC j THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN TRY(ASM_REWRITE_TAC[]);;

(* Lean: singleton_bar *)
let C1089LSNI_SINGLETON_BAR = prove
 (`forall qc qs qu qv qa x.
     c1089lsni_input qc qs qu qv qa /\ &28 / &25 <= x /\ x <= &87 / &50
     ==> linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
                linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c1089lsni_input qc qs qu qv qa` THEN SIMP_TAC[c1089lsni_input];
    ALL_TAC] THEN
  MP_TAC(SPECL [`qc 0:real`; `qs 0:real`; `qu 0:real`; `qv 0:real`; `qa 0:real`;
                `&28 / &25`; `&1`; `&87 / &50`; `&1`; `(&50 / &31) * (x - &28 / &25)`]
    CES_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - (&50 / &31) * (x - &28 / &25)) * &28 / &25 +
    ((&50 / &31) * (x - &28 / &25)) * &87 / &50 = x /\
    (&1 - (&50 / &31) * (x - &28 / &25)) * &1 + ((&50 / &31) * (x - &28 / &25)) * &1 = &1`
    (fun th -> REWRITE_TAC[th]) THEN
  REAL_ARITH_TAC);;

(* Lean: f_alternatives *)
let C1089LSNI_F_ALTERNATIVES = prove
 (`forall qc qs qu qv qa.
     c1089lsni_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) \/
         linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&113 / &50)` MP_TAC THENL
   [C1089LSNI_FOREIGN_TAC `7` `8` THEN
    UNDISCH_TAC `c1089lsni_input qc qs qu qv qa` THEN SIMP_TAC[c1089lsni_input];
    ALL_TAC] THEN
  UNDISCH_TAC `c1089lsni_input qc qs qu qv qa` THEN REWRITE_TAC[c1089lsni_input] THEN
  MESON_TAC[]);;

(* Lean: g_alternatives *)
let C1089LSNI_G_ALTERNATIVES = prove
 (`forall qc qs qu qv qa.
     c1089lsni_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) \/
         linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&12 / &5)` MP_TAC THENL
   [C1089LSNI_FOREIGN_TAC `7` `8` THEN
    UNDISCH_TAC `c1089lsni_input qc qs qu qv qa` THEN SIMP_TAC[c1089lsni_input];
    ALL_TAC] THEN
  UNDISCH_TAC `c1089lsni_input qc qs qu qv qa` THEN REWRITE_TAC[c1089lsni_input] THEN
  MESON_TAC[]);;

(* the chart pullY (pullX Q) *)
let C1089LSNI_CHART = prove
 (`forall c s u v a x y.
     linside (--c) (--s) (u - &4 * c - &4 * s) (v + &4 * s - &4 * c) a x y <=>
     linside c s u v a (&4 - x) (&4 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: outward_points *)
let C1089LSNI_OUTWARD_POINTS = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lsni_input qc qs qu qv qa /\
     ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&1) /\
     ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2)
     ==> linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&77 / &50) (&201 / &100) /\
         linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&3 / &2) (&51 / &25) /\
         linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&59 / &40) (&17 / &8)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `qc 4 * qc 4 + qs 4 * qs 4 = &1 /\ &1 < qa 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ARITH_TAC;
      UNDISCH_TAC `c1089lsni_input qc qs qu qv qa` THEN
      SIMP_TAC[c1089lsni_input; ARITH_RULE `4 < 12`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&457 / &500) (&2)`
    ASSUME_TAC THENL
   [C1089LSNI_FOREIGN_TAC `4` `8` THEN
    UNDISCH_TAC `c1089lsni_input qc qs qu qv qa` THEN SIMP_TAC[c1089lsni_input];
    ALL_TAC] THEN
  SUBGOAL_THEN `forall z. &113 / &50 <= z ==> z <= &14 / &5
                    ==> ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&4 - z) (&1)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                  `qa:num->real`; `&4 - z`] C1089LSNI_SINGLETON_BAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    UNDISCH_TAC `linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&4 - z) (&1)` THEN
    REWRITE_TAC[] THEN C1089LSNI_FOREIGN_TAC `4` `0`;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&8 / &5) /\
    ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&457 / &500) (&1)`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c1089lsni_input qc qs qu qv qa` THEN SIMP_TAC[c1089lsni_input];
    ALL_TAC] THEN
  MAP_EVERY (fun th ->
    MP_TAC(SPECL [`--(qc 4):real`; `--(qs 4):real`; `qu 4 - &4 * qc 4 - &4 * qs 4`;
                  `qv 4 + &4 * qs 4 - &4 * qc 4`; `qa 4:real`] th))
    [OCOBP_POINT_ORIGINAL; OCSDP_OUTWARD_OF_BAR; CCOP_POINT_ORIGINAL] THEN
  REWRITE_TAC[C1089LSNI_CHART; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < qa 4 /\
    (forall z. &113 / &50 <= z ==> z <= &14 / &5
         ==> ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&4 - z) (&1))`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[]);;

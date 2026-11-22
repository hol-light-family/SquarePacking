(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1090/NESelectionOwners.lean        *)
(* (namespace N12Compact.Completion.OtherCases.C1090.NESelectionOwners).    *)
(* Literal C1090 application of NE-SELECTION: S=Q5, E=Q6, NW=Q7, SE corner  *)
(* Q1, bottom Q9, right Q10.                                                 *)
(* q : Fin 12 -> OpenSquare is written as five coordinate functions          *)
(*   qc qs qu qv qa : num -> real,  q i = (qc i, qs i, qu i, qv i, qa i),    *)
(* i < 12.  The OpenSquare field unit_normal is the separate hypothesis      *)
(*   !i. i < 12 ==> qc i * qc i + qs i * qs i = &1   (side_pos follows from  *)
(* the side field).                                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_OtherCases_C1090_NESelection.ml";;

(* Lean: Data (structure) *)
let c1090neso_data = new_definition
 `c1090neso_data (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&3) (&8 / &5) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&1) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&1543 / &500) (&1) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&1543 / &500) (&2) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&113 / &50) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&12 / &5) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&113 / &50) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&14 / &5) (&1) /\
    (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2) (&113 / &50) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3)) /\
    (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&2) \/
     linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3))`;;

(* Lean: bottom_bar *)
let C1090NESO_BOTTOM_BAR = prove
 (`forall qc qs qu qv qa x. c1090neso_data qc qs qu qv qa /\ &113 / &50 <= x /\ x <= &14 / &5
     ==> linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) x (&1)`,
  REWRITE_TAC[c1090neso_data] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&14 / &5`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* apart, used as  h.apart i j _ _ _ <own, point> *)
let C1090NESO_FOREIGN = prove
 (`forall qc qs qu qv qa i j x y.
     c1090neso_data qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (qc j) (qs j) (qu j) (qv j) (qa j) x y
     ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REWRITE_TAC[c1090neso_data] THEN MESON_TAC[]);;

(* Lean: input *)
let C1090NESO_INPUT = prove
 (`forall qc qs qu qv qa. c1090neso_data qc qs qu qv qa
     ==> occ1090nes_input (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (qc 6) (qs 6) (qu 6) (qv 6) (qa 6)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`]
                C1090NESO_BOTTOM_BAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[c1090neso_data] o
    check (can (term_match [] `c1090neso_data qc qs qu qv qa`) o concl)) THEN
  REWRITE_TAC[occ1090nes_input; ldisj] THEN REPEAT CONJ_TAC THEN
  FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    ASM_SIMP_TAC[ARITH_RULE `5 < 12 /\ 6 < 12`] THEN NO_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`5`; `6`] o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `~(i:num = j)`)) (concl th))) THEN
    CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[] THEN NO_TAC;
    TRY (GEN_TAC THEN DISCH_TAC THEN DISCH_TAC) THEN
    MATCH_MP_TAC C1090NESO_FOREIGN THEN
    FIRST (map (fun j -> EXISTS_TAC (mk_small_numeral j) THEN ASM_SIMP_TAC[] THEN
                         CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) [1; 10; 9; 7])]);;

(* Lean: selection *)
let C1090NESO_SELECTION = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ c1090neso_data qc qs qu qv qa
     ==> linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3) /\
         (linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&2) ==>
          linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&12 / &5) (&3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPECL (map (fun f -> mk_comb(f, `5`)) [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`] @
                 map (fun f -> mk_comb(f, `6`)) [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`])
         OCC1090NES_SELECTION) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_SIMP_TAC[C1090NESO_INPUT; ARITH_RULE `5 < 12 /\ 6 < 12`] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1090neso_data]) THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `5` th) THEN MP_TAC(SPEC `6` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[] THEN REAL_ARITH_TAC);;

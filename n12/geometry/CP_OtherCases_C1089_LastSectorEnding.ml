(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastSectorEnding.lean         *)
(* (namespace N12Compact.Completion.OtherCases.C1089.LastSectorEnding).     *)
(* Source-level geometric ending of the final C1089 sector (not the whole    *)
(* case exclusion).  q : Fin 12 -> OpenSquare as qc qs qu qv qa : num->real *)
(* (i < 12); unit normals are the hypothesis                               *)
(*   !i. i < 12 ==> qc i * qc i + qs i * qs i = &1.                         *)
(* LastSectorExtra.Input: c1089lse_input; LastSectorExtra.impossible:       *)
(* C1089LSE_IMPOSSIBLE; WallOrigins.*: OC1089WO_*.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastSectorExtra.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallOrigins.ml";;

(* Lean: Input (structure) *)
let c1089lsen_input = new_definition
 `c1089lsen_input (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
    (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&1) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    (forall i. i < 12 ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) (&457 / &500) (&1)) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&457 / &500) /\
    linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&1) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&1543 / &500) /\
    linside (qc 2) (qs 2) (qu 2) (qv 2) (qa 2) (&3) (&3) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&3) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&8 / &5) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&87 / &50) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&5 / &2) (&2) /\
    linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&3 / &2) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&113 / &50) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&3) (&12 / &5) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&113 / &50) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&12 / &5) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&457 / &500) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&12 / &5) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&113 / &50) (&1) /\
    linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&14 / &5) (&1) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&1543 / &500) (&2) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&8 / &5) /\
    linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&2) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&12 / &5) (&3) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&113 / &50) (&3)`;;

let C1089LSEN_APART = prove
 (`forall qc qs qu qv qa i j x y.
     c1089lsen_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
           linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)`,
  REWRITE_TAC[c1089lsen_input] THEN MESON_TAC[]);;

let C1089LSEN_SAME = prove
 (`forall qc qs qu qv qa i j.
     c1089lsen_input qc qs qu qv qa /\ i < 12 /\ j < 12 ==> qa i = qa j`,
  REWRITE_TAC[c1089lsen_input] THEN MESON_TAC[]);;

let C1089LSEN_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[ldisj] THEN REPEAT GEN_TAC THEN MATCH_MP_TAC C1089LSEN_APART THEN
           ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         MATCH_MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`;
           `qv:num->real`] C1089LSEN_SAME) THEN CONV_TAC NUM_REDUCE_CONV THEN
           REWRITE_TAC[] THEN FIRST_ASSUM ACCEPT_TAC;
         RASM_ARITH_TAC];;

let C1089LSEN_Q i =
  map (fun f -> mk_comb(mk_var(f, `:num->real`), mk_small_numeral i))
    ["qc"; "qs"; "qu"; "qv"; "qa"];;

let C1089LSEN_APPLY_TAC th idx =
  MP_TAC(SPECL (List.concat (map C1089LSEN_Q idx)) th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089LSEN_SIDE_TAC; DISCH_TAC];;

(* Lean: reduced_input *)
let C1089LSEN_REDUCED_INPUT = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lsen_input qc qs qu qv qa
     ==> c1089lse_input qc qs qu qv qa`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1089lsen_input] o check (fun th ->
    fst(strip_comb(concl th)) = `c1089lsen_input`)) THEN
  (fun (asl,w as g) ->
    let ths = filter (fun th -> match strip_forall(concl th) with
      | ([v], t) -> is_imp t && lhand t = mk_binop `(<):num->num->bool` v `12`
      | _ -> false) (map snd asl) in
    MAP_EVERY (fun i ->
      let n = mk_small_numeral i in
      let lt = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` n `12`)) in
      MAP_EVERY (fun th -> ASSUME_TAC(MP (SPEC n th) lt)) ths) (0--11) g) THEN
  C1089LSEN_APPLY_TAC OC1089WO_LEFT_ADVANCE [8; 4; 7] THEN
  C1089LSEN_APPLY_TAC OC1089WO_RIGHT_LOW [10; 6; 5] THEN
  C1089LSEN_APPLY_TAC OC1089WO_BOTTOM_ORIGIN [9; 1; 10] THEN
  C1089LSEN_APPLY_TAC OC1089WO_TOP_ORIGIN_OF_ORDINARY [6; 5; 10; 2; 11] THEN
  C1089LSEN_APPLY_TAC OC1089WO_TOP_ADVANCE [11; 7; 6] THEN
  REWRITE_TAC[c1089lse_input; oc1089lssj_base] THEN
  REPEAT CONJ_TAC THEN C1089LSEN_SIDE_TAC);;

(* Lean: impossible *)
let C1089LSEN_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lsen_input qc qs qu qv qa
     ==> false`,
  MESON_TAC[C1089LSEN_REDUCED_INPUT; C1089LSE_IMPOSSIBLE]);;

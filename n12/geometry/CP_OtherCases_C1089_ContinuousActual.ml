(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ContinuousActual.lean         *)
(* (N12Compact.Completion.OtherCases.C1089.ContinuousActual).               *)
(* The two actual-owner applications of C1089-CONTINUOUS-REDUCTION §5.      *)
(* q : Fin 12 -> OpenSquare is written as five coordinate functions          *)
(*   qc qs qu qv qa : num -> real,  q i = (qc i, qs i, qu i, qv i, qa i),    *)
(* i < 12; the unit normals are the explicit hypothesis                     *)
(*   !i. i < 12 ==> qc i * qc i + qs i * qs i = &1.                         *)
(* southeastChart Q = translate (pullY Q) 2 2 of Q = (c, s, u, v, a) is      *)
(*   (c, --s, u - &2 * c - &2 * s, --v - a - &2 * s + &2 * c, a),            *)
(*   inside x y <=> Q inside (x + 2) (2 - y);                               *)
(* northwestChart Q = translate (pullY (pullSwap Q)) 2 2 is                  *)
(*   (s, --c, u - &2 * c - &2 * s, v + &2 * s - &2 * c, a),                  *)
(*   inside x y <=> Q inside (2 - y) (x + 2).                               *)
(* ContinuousCenter.points: C1089CC_POINTS.                                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousCenter.ml";;

(* Lean: southeast_inside (private) *)
let C1089CA_SOUTHEAST_INSIDE = prove
 (`forall c s u v a x y.
     linside c (--s) (u - &2 * c - &2 * s) (--v - a - &2 * s + &2 * c) a x y <=>
     linside c s u v a (x + &2) (&2 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: northwest_inside (private) *)
let C1089CA_NORTHWEST_INSIDE = prove
 (`forall c s u v a x y.
     linside s (--c) (u - &2 * c - &2 * s) (v + &2 * s - &2 * c) a x y <=>
     linside c s u v a (&2 - y) (x + &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1089CA_CENTERS = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcy c (--s) (u - &2 * c - &2 * s) (--v - a - &2 * s + &2 * c) a =
         &2 - lcy c s u v a /\
         lcy s (--c) (u - &2 * c - &2 * s) (v + &2 * s - &2 * c) a =
         &2 - lcx c s u v a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcx; lcy] THEN CONV_TAC REAL_RING);;

let C1089CA_APART = prove
 (`forall qc qs qu qv qa i j x y.
     (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
            ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                        linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
     i < 12 /\ j < 12 /\ ~(i = j)
     ==> ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
           linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)`,
  MESON_TAC[]);;

(* the side goals of the ContinuousCenter input after the chart rewrite *)
let C1089CA_SIDE_TAC =
  let apart_tac =
    REPEAT GEN_TAC THEN MATCH_MP_TAC C1089CA_APART THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV in
  let wall_tac =
    REPEAT GEN_TAC THEN DISCH_THEN(fun p ->
      FIRST_ASSUM(fun l -> if is_comb(concl l) && fst(strip_comb(concl l)) = `lcont`
        then MP_TAC(MATCH_MP (REWRITE_RULE[lcont] l) p) else NO_TAC)) THEN
    REAL_ARITH_TAC in
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         apart_tac THEN NO_TAC;
         wall_tac THEN NO_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
           FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
           ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
         ASM_REAL_ARITH_TAC];;

(* per-index facts: instantiate every hypothesis !i. i < 12 ==> P i *)
let C1089CA_INDEX_TAC idx (asl,w as g) =
  let ths = filter (fun th -> match strip_forall(concl th) with
      | ([v], t) -> is_imp t && lhand t = mk_binop `(<):num->num->bool` v `12`
      | _ -> false) (map snd asl) in
  MAP_EVERY (fun i ->
    let n = mk_small_numeral i in
    let lt = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` n `12`)) in
    MAP_EVERY (fun th -> ASSUME_TAC(MP (SPEC n th) lt)) ths) idx g;;

(* the facts qa i0 = qa j for the listed j *)
let C1089CA_SAME_TAC i0 idx (asl,w as g) =
  let same = find (fun th -> match strip_forall(concl th) with
      | ([_;_], t) -> is_imp t && is_eq(rand t) | _ -> false) (map snd asl) in
  MAP_EVERY (fun j ->
    let lt = EQT_ELIM(NUM_REDUCE_CONV
      (mk_conj(mk_binop `(<):num->num->bool` (mk_small_numeral i0) `12`,
               mk_binop `(<):num->num->bool` (mk_small_numeral j) `12`))) in
    ASSUME_TAC(MP (SPECL [mk_small_numeral i0; mk_small_numeral j] same) lt)) idx g;;

(* Lean: southeast *)
let C1089CA_SOUTHEAST = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     (forall i. i < 12 ==> &1 < qa i) /\
     (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
     (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
     (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
            ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                        linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&47 / &20) (&33 / &20) /\
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&87 / &50) /\
     linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&113 / &50) (&2) /\
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
     linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&1543 / &500) (&2) /\
     linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&87 / &50) /\
     lcy (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) <= &2 /\
     linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&2) (&457 / &500) /\
     linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&12 / &5) (&1) /\
     linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
     linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&1543 / &500) (&1) /\
     linside (qc 1) (qs 1) (qu 1) (qv 1) (qa 1) (&3) (&1)
     ==> linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2) (&2) /\
         linside (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) (&3) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1089CA_INDEX_TAC [5; 10; 9; 1] THEN
  SUBGOAL_THEN `~linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&33 / &20) (&33 / &20) /\
                ~linside (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) (&87 / &50) (&1)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
        `qa:num->real`; `5`; `4`; `&33 / &20`; `&33 / &20`] C1089CA_APART);
      MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
        `qa:num->real`; `9`; `0`; `&87 / &50`; `&1`] C1089CA_APART)] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`qc 5:real`; `--(qs 5):real`; `qu 5 - &2 * qc 5 - &2 * qs 5`;
    `--(qv 5) - qa 5 - &2 * qs 5 + &2 * qc 5`; `qa 5:real`;
    `qc 10:real`; `--(qs 10):real`; `qu 10 - &2 * qc 10 - &2 * qs 10`;
    `--(qv 10) - qa 10 - &2 * qs 10 + &2 * qc 10`; `qa 10:real`;
    `qc 9:real`; `--(qs 9):real`; `qu 9 - &2 * qc 9 - &2 * qs 9`;
    `--(qv 9) - qa 9 - &2 * qs 9 + &2 * qc 9`; `qa 9:real`;
    `qc 1:real`; `--(qs 1):real`; `qu 1 - &2 * qc 1 - &2 * qs 1`;
    `--(qv 1) - qa 1 - &2 * qs 1 + &2 * qc 1`; `qa 1:real`] C1089CC_POINTS) THEN
  REWRITE_TAC[c1089cc_input; ldisj; C1089CA_SOUTHEAST_INSIDE;
    MATCH_MP C1089CA_CENTERS (ASSUME `qc 10 * qc 10 + qs 10 * qs 10 = &1`)] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  C1089CA_SAME_TAC 5 [10; 9; 1] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089CA_SIDE_TAC; SIMP_TAC[]]);;

(* Lean: northwest *)
let C1089CA_NORTHWEST = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     (forall i. i < 12 ==> &1 < qa i) /\
     (forall i j. i < 12 /\ j < 12 ==> qa i = qa j) /\
     (forall i. i < 12 ==> lcont (qc i) (qs i) (qu i) (qv i) (qa i)) /\
     (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
            ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                        linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) /\
     linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50) /\
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
     linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500) /\
     linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&87 / &50) (&3) /\
     lcx (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) <= &2 /\
     linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
     linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&12 / &5) /\
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
     linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&1543 / &500) /\
     linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&3)
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&2) /\
         linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1089CA_INDEX_TAC [7; 11; 8; 3] THEN
  SUBGOAL_THEN `~linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&33 / &20) /\
                ~linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&87 / &50)`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
        `qa:num->real`; `7`; `4`; `&33 / &20`; `&33 / &20`] C1089CA_APART);
      MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
        `qa:num->real`; `8`; `4`; `&1`; `&87 / &50`] C1089CA_APART)] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPECL
   [`qs 7:real`; `--(qc 7):real`; `qu 7 - &2 * qc 7 - &2 * qs 7`;
    `qv 7 + &2 * qs 7 - &2 * qc 7`; `qa 7:real`;
    `qs 11:real`; `--(qc 11):real`; `qu 11 - &2 * qc 11 - &2 * qs 11`;
    `qv 11 + &2 * qs 11 - &2 * qc 11`; `qa 11:real`;
    `qs 8:real`; `--(qc 8):real`; `qu 8 - &2 * qc 8 - &2 * qs 8`;
    `qv 8 + &2 * qs 8 - &2 * qc 8`; `qa 8:real`;
    `qs 3:real`; `--(qc 3):real`; `qu 3 - &2 * qc 3 - &2 * qs 3`;
    `qv 3 + &2 * qs 3 - &2 * qc 3`; `qa 3:real`] C1089CC_POINTS) THEN
  REWRITE_TAC[c1089cc_input; ldisj; C1089CA_NORTHWEST_INSIDE;
    MATCH_MP C1089CA_CENTERS (ASSUME `qc 11 * qc 11 + qs 11 * qs 11 = &1`)] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  C1089CA_SAME_TAC 7 [11; 8; 3] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089CA_SIDE_TAC; SIMP_TAC[]]);;

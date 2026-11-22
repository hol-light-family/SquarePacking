(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMWallOrderCycle.lean                  *)
(* (namespace N12Compact.C1092MPPMWallOrderCycle; Lean header: "No compiler  *)
(* replay was requested for this source addition").  The literal four-wall   *)
(* cancellation.  q : Fin 12 -> OpenSquare is the five coordinate functions  *)
(* qc qs qu qv qa (unit normals of the used squares 8..11 explicit);         *)
(* central : Fin 4 -> OpenSquare is cc cs cu cv ca : num->real (unit normals *)
(* explicit), angle is ang : num->real.  Statements "forall i : Fin 4" are   *)
(* the conjunction over i = 0..3; chart i is the OCaml term map              *)
(* c1092mwoc_chart i (translated 2 2 after the pulls), bottomRole / leftRole *)
(* are the OCaml lists c1092mwoc_bottomRole / c1092mwoc_leftRole and         *)
(* centerPairs is c1092mwoc_centerPairs (a list of real-pair terms).         *)
(* RetainingSector = c1092mwoc_retaining; its order = C1092SLO_ORDER.        *)
(* Tag C1092MWOC_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShallowLeftOrder.ml";;

(* Lean: bottomRole, leftRole *)
let c1092mwoc_bottomRole = [9; 10; 11; 8];;
let c1092mwoc_leftRole = [8; 9; 10; 11];;

(* the square q i as a 5-tuple of terms *)
let c1092mwoc_q i = map (fun f -> mk_comb(f, mk_small_numeral i))
  [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

let c1092mwoc_map tms [c; s; u; v; a] =
  map (fun t -> rand(concl(REWRITE_CONV[] (vsubst [c,`c:real`; s,`s:real`; u,`u:real`;
                                                    v,`v:real`; a,`a:real`] t)))) tms;;
let c1092mwoc_pullx = c1092mwoc_map [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;
let c1092mwoc_pully = c1092mwoc_map [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let c1092mwoc_pullsw = c1092mwoc_map [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;
let c1092mwoc_tr22 = c1092mwoc_map
  [`c:real`; `s:real`; `u - (c * &2 + s * &2)`; `v - (--s * &2 + c * &2)`; `a:real`];;

(* Lean: chart *)
let c1092mwoc_chart i q =
  match i with
    0 -> c1092mwoc_tr22 q
  | 1 -> c1092mwoc_tr22 (c1092mwoc_pully (c1092mwoc_pullsw q))
  | 2 -> c1092mwoc_tr22 (c1092mwoc_pullx (c1092mwoc_pully q))
  | _ -> c1092mwoc_tr22 (c1092mwoc_pullx (c1092mwoc_pullsw q));;

let c1092mwoc_lcx q = list_mk_comb(`lcx`, q);;
let c1092mwoc_lcy q = list_mk_comb(`lcy`, q);;

(* Lean: centerPairs *)
let c1092mwoc_centerPairs =
  [`lcx (qc 9) (qs 9) (qu 9) (qv 9) (qa 9) - &2`, `lcy (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) - &2`;
   `lcy (qc 10) (qs 10) (qu 10) (qv 10) (qa 10) - &2`, `&2 - lcx (qc 9) (qs 9) (qu 9) (qv 9) (qa 9)`;
   `&2 - lcx (qc 11) (qs 11) (qu 11) (qv 11) (qa 11)`, `&2 - lcy (qc 10) (qs 10) (qu 10) (qv 10) (qa 10)`;
   `&2 - lcy (qc 8) (qs 8) (qu 8) (qv 8) (qa 8)`, `lcx (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) - &2`];;

let c1092mwoc_bottom i = c1092mwoc_chart i (c1092mwoc_q (el i c1092mwoc_bottomRole));;
let c1092mwoc_left i = c1092mwoc_chart i (c1092mwoc_q (el i c1092mwoc_leftRole));;

let C1092MWOC_UNIT =
  `forall i. 8 <= i /\ i < 12 ==> qc i * qc i + qs i * qs i = &1`;;

(* Lean: center_pair (one theorem per i : Fin 4) *)
let C1092MWOC_CENTER_PAIR =
  Array.init 4 (fun i ->
    let x, y = el i c1092mwoc_centerPairs in
    let gl = mk_imp(C1092MWOC_UNIT,
      mk_conj(mk_eq(c1092mwoc_lcx (c1092mwoc_bottom i), x),
              mk_eq(c1092mwoc_lcy (c1092mwoc_left i), y))) in
    prove(list_mk_forall([`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                          `qa:num->real`], gl),
      REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[lcx; lcy] THEN CONJ_TAC THEN
      MAP_EVERY (fun j -> MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC (mk_small_numeral j)
        (ASSUME C1092MWOC_UNIT)))) [8; 9; 10; 11] THEN
      CONV_TAC REAL_RING));;

let c1092mwoc_orders =
  list_mk_conj (map (fun i ->
    mk_comb(mk_comb(`(<):real->real->bool`, `&0`),
      mk_comb(mk_comb(`(+):real->real->real`, c1092mwoc_lcx (c1092mwoc_bottom i)),
              c1092mwoc_lcy (c1092mwoc_left i)))) [0; 1; 2; 3]);;

let C1092MWOC_VARS = [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

(* Lean: cyclic_order_impossible *)
let C1092MWOC_CYCLIC_ORDER_IMPOSSIBLE = prove
 (list_mk_forall(C1092MWOC_VARS,
    mk_imp(mk_conj(C1092MWOC_UNIT, c1092mwoc_orders), `false`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun i -> MP_TAC(UNDISCH(SPEC_ALL C1092MWOC_CENTER_PAIR.(i)))) [0; 1; 2; 3] THEN
  REPEAT STRIP_TAC THEN
  RASM_ARITH_TAC);;

(* Lean: RetainingSector (structure) *)
let c1092mwoc_retaining = new_definition
 `c1092mwoc_retaining (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                      (cB:real) (sB:real) (uB:real) (vB:real) (aB:real)
                      (cL:real) (sL:real) (uL:real) (vL:real) (aL:real) (x:real) <=>
    &1 < aC /\ aC = aB /\ aC = aL /\ c1092sbo_data cC sC uC vC aC x /\
    linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
    linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
    (forall u v. linside cB sB uB vB aB u v ==> --(&2) <= v) /\
    linside cL sL uL vL aL (--(&543 / &500)) (&0) /\
    linside cL sL uL vL aL (--(&1)) (&0) /\
    (forall u v. linside cL sL uL vL aL u v ==> --(&2) <= u) /\
    ldisj cC sC uC vC aC cB sB uB vB aB /\
    ldisj cC sC uC vC aC cL sL uL vL aL`;;

(* Lean: RetainingSector.order *)
let C1092MWOC_RETAINING_ORDER = prove
 (`forall cC sC uC vC aC cB sB uB vB aB cL sL uL vL aL x.
     cC * cC + sC * sC = &1 /\ cB * cB + sB * sB = &1 /\ cL * cL + sL * sL = &1 /\
     c1092mwoc_retaining cC sC uC vC aC cB sB uB vB aB cL sL uL vL aL x
     ==> &0 < lcx cB sB uB vB aB + lcy cL sL uL vL aL`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mwoc_retaining] THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092SLO_ORDER THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `x:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC));;

let c1092mwoc_central i = map (fun f -> mk_comb(f, mk_small_numeral i))
  [`cc:num->real`; `cs:num->real`; `cu:num->real`; `cv:num->real`; `ca:num->real`];;
let c1092mwoc_sector i =
  list_mk_comb(`c1092mwoc_retaining`,
    c1092mwoc_central i @ c1092mwoc_bottom i @ c1092mwoc_left i @ [mk_comb(`ang:num->real`, mk_small_numeral i)]);;
let c1092mwoc_order i =
  mk_comb(mk_comb(`(<):real->real->bool`, `&0`),
    mk_comb(mk_comb(`(+):real->real->real`, c1092mwoc_lcx (c1092mwoc_bottom i)),
            c1092mwoc_lcy (c1092mwoc_left i)));;
let C1092MWOC_CUNIT = `forall i. i < 4 ==> cc i * cc i + cs i * cs i = &1`;;
let C1092MWOC_CVARS = [`cc:num->real`; `cs:num->real`; `cu:num->real`; `cv:num->real`; `ca:num->real`; `ang:num->real`];;

(* the order of sector i from its retaining data *)
let C1092MWOC_SECTOR_ORDER = Array.init 4 (fun i ->
  prove(list_mk_forall(C1092MWOC_VARS @ C1092MWOC_CVARS,
          mk_imp(list_mk_conj[C1092MWOC_UNIT; C1092MWOC_CUNIT; c1092mwoc_sector i], c1092mwoc_order i)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1092MWOC_RETAINING_ORDER THEN
    MAP_EVERY EXISTS_TAC (c1092mwoc_central i @ [mk_comb(`ang:num->real`, mk_small_numeral i)]) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY (fun j -> MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC (mk_small_numeral j)
      (ASSUME C1092MWOC_UNIT)))) [8; 9; 10; 11] THEN
    MP_TAC(CONV_RULE NUM_REDUCE_CONV (SPEC (mk_small_numeral i) (ASSUME C1092MWOC_CUNIT))) THEN
    REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) || is_comb(concl th) &&
      fst(strip_comb(concl th)) = `c1092mwoc_retaining` then ALL_TAC else MP_TAC th)) THEN
    CONV_TAC REAL_RING));;

(* Lean: retaining_cycle_impossible *)
let C1092MWOC_RETAINING_CYCLE_IMPOSSIBLE = prove
 (list_mk_forall(C1092MWOC_VARS @ C1092MWOC_CVARS,
    mk_imp(list_mk_conj[C1092MWOC_UNIT; C1092MWOC_CUNIT;
                        list_mk_conj(map c1092mwoc_sector [0; 1; 2; 3])], `false`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(SPEC_ALL C1092MWOC_CYCLIC_ORDER_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FIRST(map (fun i -> MATCH_MP_TAC(SPEC_ALL C1092MWOC_SECTOR_ORDER.(i)) THEN
    ASM_REWRITE_TAC[] THEN NO_TAC) [0; 1; 2; 3]));;

(* Lean: mixed_forward_cycle_impossible *)
let C1092MWOC_MIXED_FORWARD_CYCLE_IMPOSSIBLE = prove
 (list_mk_forall(C1092MWOC_VARS @ C1092MWOC_CVARS,
    mk_imp(list_mk_conj[C1092MWOC_UNIT; C1092MWOC_CUNIT;
             list_mk_conj(map (fun i -> mk_disj(c1092mwoc_sector i, c1092mwoc_order i)) [0; 1; 2; 3])],
           `false`)),
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (MAP_EVERY ASSUME_TAC o CONJUNCTS))) THEN
  MATCH_MP_TAC(SPEC_ALL C1092MWOC_CYCLIC_ORDER_IMPOSSIBLE) THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN FIRST(map (fun i ->
    FIRST_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      rand(concl th) = c1092mwoc_order i)) THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC(SPEC_ALL C1092MWOC_SECTOR_ORDER.(i)) THEN ASM_REWRITE_TAC[] THEN NO_TAC) [0; 1; 2; 3]));;

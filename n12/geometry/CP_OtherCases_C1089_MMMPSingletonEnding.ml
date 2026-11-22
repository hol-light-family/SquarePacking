(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/MMMPSingletonEnding.lean      *)
(* (N12Compact.Completion.OtherCases.C1089.MMMPSingletonEnding).             *)
(* C1089-MMMP-SINGLETON-ENDING from the literal actual-owner core.  The      *)
(* Lean header says "It is uncompiled source, not ExcludesCase1089".         *)
(* q : Fin 12 -> OpenSquare is written as five coordinate functions          *)
(*   qc qs qu qv qa : num -> real  (q i = (qc i, qs i, qu i, qv i, qa i)),   *)
(* i < 12; the OpenSquare invariant unit_normal of each q i is the explicit *)
(* hypothesis  !i. i < 12 ==> qc i * qc i + qs i * qs i = &1  (side_pos      *)
(* follows from the field side).  InsideContainer is lcont; pullX / pullY /  *)
(* pullSwap are the explicit squares of LINSIDE_PULLX / _PULLY / _PULLSW.    *)
(* inside_segment is CES_INSIDE_SEGMENT, C1092MixedSpan.impossible is        *)
(* C1092MS_IMPOSSIBLE, C981CompletionCrosspoint.point is C981CP_POINT,       *)
(* WallOrigins.top_left_advance is OC1089WO_TOP_LEFT_ADVANCE,                *)
(* InnerCornerObstruction.corner_excluded_original is                        *)
(* OCICOM_CORNER_EXCLUDED_ORIGINAL, InwardPoint / OutwardPoint.point_original *)
(* are CCIP_POINT_ORIGINAL / CCOP_POINT_ORIGINAL.  Tag OC1089MSE_.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallOrigins.ml";;
needs "n12/geometry/CP_OtherCases_InnerCornerObstruction_Main.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: Input (structure) *)
let oc1089mse_input = new_definition
 `oc1089mse_input (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    (forall i. i < 12 ==> &1 < qa i) /\
    lcont (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) /\
    (forall i j. i < 12 /\ j < 12 /\ ~(i = j)
           ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                       linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&457 / &500) (&1) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&33 / &20) (&33 / &20) /\
    (linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) \/
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&8 / &5) (&1) \/
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2) (&87 / &50)) /\
    (linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&8 / &5) \/
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&1) \/
     linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2)) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&47 / &20) (&47 / &20) /\
    linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&113 / &50) (&3) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&2) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&2) (&1543 / &500) /\
    linside (qc 11) (qs 11) (qu 11) (qv 11) (qa 11) (&8 / &5) (&3)`;;

let OC1089MSE_UNITS = `forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1`;;
let OC1089MSE_IN = `oc1089mse_input qc qs qu qv qa`;;

let oc1089mse_sq i =
  let n = mk_small_numeral i in
  map (fun f -> mk_comb(mk_var(f, `:num->real`), n)) ["qc"; "qs"; "qu"; "qv"; "qa"];;
let oc1089mse_pull th tup =
  match tup with
    [c; s; u; v; a] ->
      let t = SPECL [c; s; u; v; a; `x:real`; `y:real`] th in
      let args = snd(strip_comb(lhs(concl t))) in
      [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args]
  | _ -> failwith "oc1089mse_pull";;
let oc1089mse_lin i x y = list_mk_comb(`linside`, oc1089mse_sq i @ [x; y]);;

(* the apart field at two literal indices *)
let OC1089MSE_APART = prove
 (`forall qc qs qu qv qa i j x y.
     oc1089mse_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j) /\
     linside (qc j) (qs j) (qu j) (qv j) (qa j) x y
     ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) x y`,
  REWRITE_TAC[oc1089mse_input] THEN MESON_TAC[]);;

let OC1089MSE_LDISJ = prove
 (`forall qc qs qu qv qa i j.
     oc1089mse_input qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> ldisj (qc i) (qs i) (qu i) (qv i) (qa i) (qc j) (qs j) (qu j) (qv j) (qa j)`,
  REWRITE_TAC[oc1089mse_input; ldisj] THEN MESON_TAC[]);;
let OC1089MSE_LDISJ_AT i j =
  REWRITE_RULE[ARITH] (SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`;
    `qv:num->real`; `qa:num->real`; mk_small_numeral i; mk_small_numeral j] OC1089MSE_LDISJ);;

(* ~ q i at (x, y), from the assumption that q j owns (x, y) *)
let OC1089MSE_FOREIGN i j x y =
  let th = REWRITE_RULE[ARITH] (SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`;
             `qv:num->real`; `qa:num->real`; mk_small_numeral i; mk_small_numeral j; x; y]
             OC1089MSE_APART) in
  SUBGOAL_THEN (mk_neg(oc1089mse_lin i x y)) ASSUME_TAC THENL
   [MATCH_MP_TAC th THEN ASM_REWRITE_TAC[]; ALL_TAC];;

(* unfold the input; the unit normal and side of each listed square *)
let OC1089MSE_START_TAC idx =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[oc1089mse_input] o
    check (fun th -> concl th = OC1089MSE_IN)) THEN
  MAP_EVERY (fun i ->
    MP_TAC(REWRITE_RULE[ARITH] (SPEC (mk_small_numeral i) (ASSUME OC1089MSE_UNITS))) THEN
    MP_TAC(REWRITE_RULE[ARITH] (SPEC (mk_small_numeral i)
      (ASSUME `forall i. i < 12 ==> &1 < qa i`))) THEN REPEAT DISCH_TAC) idx;;

let OC1089MSE_APPLY th args =
  let cv = REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
           ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let th' = CONV_RULE(LAND_CONV cv THENC TRY_CONV(RAND_CONV cv)) (SPECL args th) in
  MP_TAC th' THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; ASM_REAL_ARITH_TAC];
    REWRITE_TAC[] THEN TRY(FIRST_ASSUM ACCEPT_TAC)];;

(* Lean: singleton_bar *)
let OC1089MSE_SINGLETON_BAR = prove
 (`forall qc qs qu qv qa. oc1089mse_input qc qs qu qv qa
     ==> forall x. &28 / &25 <= x /\ x <= &87 / &50
             ==> linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) x (&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[oc1089mse_input] THEN
  DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL (oc1089mse_sq 0 @ [`&28 / &25`; `&1`; `&87 / &50`; `&1`;
                `(&50 / &31) * (x - &28 / &25)`]) CES_INSIDE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* Lean: southwest_pair *)
let OC1089MSE_SOUTHWEST_PAIR = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ oc1089mse_input qc qs qu qv qa
     ==> linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
         linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&8 / &5)`,
  OC1089MSE_START_TAC [4] THEN
  MP_TAC(SPEC `&8 / &5` (MATCH_MP OC1089MSE_SINGLETON_BAR (ASSUME OC1089MSE_IN))) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN
  OC1089MSE_FOREIGN 4 0 `&87 / &50` `&1` THEN
  OC1089MSE_FOREIGN 4 0 `&8 / &5` `&1` THEN
  OC1089MSE_FOREIGN 4 7 `&87 / &50` `&2` THEN
  SUBGOAL_THEN (oc1089mse_lin 4 `&1` `&8 / &5`) ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (oc1089mse_lin 4 `&1` `&87 / &50`) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN (oc1089mse_lin 4 `&2` `&87 / &50`) ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  OC1089MSE_APPLY C1092MS_IMPOSSIBLE (oc1089mse_pull LINSIDE_PULLX (oc1089mse_sq 4)));;

(* Lean: northwest_crosspoint *)
let OC1089MSE_NORTHWEST_CROSSPOINT = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ oc1089mse_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&3 / &2) (&2)`,
  OC1089MSE_START_TAC [7; 11] THEN
  MP_TAC(SPECL (oc1089mse_sq 11 @ oc1089mse_sq 6 @ oc1089mse_sq 7) OC1089WO_TOP_LEFT_ADVANCE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC (OC1089MSE_LDISJ_AT 11 6) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC (OC1089MSE_LDISJ_AT 11 7) THEN ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN (oc1089mse_lin 11 `&3 / &2` `&3`) ASSUME_TAC THENL
   [MP_TAC(SPECL (oc1089mse_sq 11 @ [`&36 / &25`; `&3`; `&8 / &5`; `&3`; `&3 / &8`])
      CES_INSIDE_SEGMENT) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  OC1089MSE_FOREIGN 7 6 `&47 / &20` `&47 / &20` THEN
  OC1089MSE_FOREIGN 7 4 `&33 / &20` `&33 / &20` THEN
  OC1089MSE_FOREIGN 7 11 `&8 / &5` `&3` THEN
  OC1089MSE_FOREIGN 7 11 `&3 / &2` `&3` THEN
  OC1089MSE_APPLY C981CP_POINT
    (oc1089mse_pull LINSIDE_PULLSW (oc1089mse_pull LINSIDE_PULLX (oc1089mse_sq 7))));;

(* Lean: southwest_corner_excluded *)
let OC1089MSE_SOUTHWEST_CORNER_EXCLUDED = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ oc1089mse_input qc qs qu qv qa
     ==> ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&1)`,
  OC1089MSE_START_TAC [4] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OC1089MSE_NORTHWEST_CROSSPOINT o
    CONJ (ASSUME OC1089MSE_UNITS)) THEN
  OC1089MSE_FOREIGN 4 0 `&28 / &25` `&1` THEN
  OC1089MSE_FOREIGN 4 8 `&457 / &500` `&2` THEN
  OC1089MSE_FOREIGN 4 7 `&3 / &2` `&2` THEN
  OC1089MSE_APPLY OCICOM_CORNER_EXCLUDED_ORIGINAL (oc1089mse_sq 4));;

(* Lean: northwest_duplicate *)
let OC1089MSE_NORTHWEST_DUPLICATE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ oc1089mse_input qc qs qu qv qa
     ==> linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&77 / &50) (&201 / &100)`,
  OC1089MSE_START_TAC [7] THEN
  OC1089MSE_FOREIGN 7 6 `&47 / &20` `&47 / &20` THEN
  OC1089MSE_FOREIGN 7 4 `&33 / &20` `&33 / &20` THEN
  OC1089MSE_FOREIGN 7 11 `&8 / &5` `&3` THEN
  OC1089MSE_APPLY CCIP_POINT_ORIGINAL
    (oc1089mse_pull LINSIDE_PULLY (oc1089mse_pull LINSIDE_PULLX (oc1089mse_sq 7))));;

(* Lean: southwest_duplicate *)
let OC1089MSE_SOUTHWEST_DUPLICATE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ oc1089mse_input qc qs qu qv qa
     ==> linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&77 / &50) (&201 / &100)`,
  OC1089MSE_START_TAC [4] THEN
  MP_TAC(MATCH_MP OC1089MSE_SOUTHWEST_PAIR (CONJ (ASSUME OC1089MSE_UNITS) (ASSUME OC1089MSE_IN))) THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP OC1089MSE_SOUTHWEST_CORNER_EXCLUDED
    (CONJ (ASSUME OC1089MSE_UNITS) (ASSUME OC1089MSE_IN))) THEN DISCH_TAC THEN
  OC1089MSE_FOREIGN 4 7 `&87 / &50` `&2` THEN
  OC1089MSE_FOREIGN 4 8 `&457 / &500` `&2` THEN
  SUBGOAL_THEN `forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~(linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&4 - z) (&1))`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `&4 - z` (MATCH_MP OC1089MSE_SINGLETON_BAR (ASSUME OC1089MSE_IN))) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(REWRITE_RULE[ARITH] (SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`;
             `qv:num->real`; `qa:num->real`; `4`; `0`; `&4 - z`; `&1`] OC1089MSE_APART)) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  OC1089MSE_APPLY CCOP_POINT_ORIGINAL
    (oc1089mse_pull LINSIDE_PULLY (oc1089mse_pull LINSIDE_PULLX (oc1089mse_sq 4))));;

(* Lean: impossible *)
let OC1089MSE_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\ oc1089mse_input qc qs qu qv qa
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OC1089MSE_SOUTHWEST_DUPLICATE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OC1089MSE_NORTHWEST_DUPLICATE) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MP_TAC(REWRITE_RULE[ARITH] (SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`;
           `qv:num->real`; `qa:num->real`; `4`; `7`; `&77 / &50`; `&201 / &100`] OC1089MSE_APART)) THEN
  ASM_REWRITE_TAC[]);;

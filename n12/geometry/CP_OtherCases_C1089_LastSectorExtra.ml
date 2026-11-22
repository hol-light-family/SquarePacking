(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastSectorExtra.lean          *)
(* (namespace N12Compact.Completion.OtherCases.C1089.LastSectorExtra).      *)
(* C1089-LAST-SECTOR-ENDING §2 with its actual foreign owners.             *)
(* q : Fin 12 -> OpenSquare as qc qs qu qv qa : num -> real (i < 12); unit   *)
(* normals are the hypothesis !i. i < 12 ==> qc i * qc i + qs i * qs i = &1. *)
(* BaseData: oc1089lssj_base; LastSectorSupportJoin.impossible:             *)
(* OC1089LSSJ_IMPOSSIBLE; OutwardBarFrame.frame_original:                   *)
(* OCOBF_FRAME_ORIGINAL (Faces: ocobp_faces of r translated by (2,2));       *)
(* OutwardBarPoint.positive_point_original: OCOBP_POSITIVE_POINT_ORIGINAL;  *)
(* SharpPointScalars.half_upper/half_lower: OCSPS_HALF_UPPER/LOWER;          *)
(* OutwardPair.impossible: OCOP_IMPOSSIBLE (t = r.s); UpperBarPoint.point:  *)
(* OCUBP_POINT; OrdinaryBarCrosspoint.southwest_point_and_left_omission:    *)
(* OBCM_SOUTHWEST_POINT_AND_LEFT_OMISSION; WallProfile.vertical_owned:      *)
(* OCWPVG_VERTICAL_OWNED; S12.inside_segment: CES_INSIDE_SEGMENT.           *)
(* Charts of Q = (c, s, u, v, a):                                           *)
(*   rotated = pullY (pullX Q): C1089LSNI_CHART (Q inside (4-x) (4-y));     *)
(*   A = (pullY r).translated 2 2 = (c, --s, u - 2c - 2s, 2c - 2s - v - a, a) *)
(*     (r inside (2+x) (2-y)); N = (pullX Q).translated 2 2: OBCM_CHART.    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastSectorSupportJoin.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarFrame.ml";;
needs "n12/geometry/CP_OtherCases_OutwardPair.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_OrdinaryBarCrosspoint_Main.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastSectorNorthwestInput.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: Input (structure extending LastSectorSupportJoin.BaseData) *)
let c1089lse_input = new_definition
 `c1089lse_input (qc:num->real) (qs:num->real) (qu:num->real) (qv:num->real) (qa:num->real) <=>
    oc1089lssj_base qc qs qu qv qa /\
    qa 4 = qa 7 /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&87 / &50) /\
    linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&1) (&8 / &5) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&1) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&28 / &25) (&1) /\
    linside (qc 0) (qs 0) (qu 0) (qv 0) (qa 0) (&87 / &50) (&1) /\
    (forall i. i < 12 ==> ~linside (qc i) (qs i) (qu i) (qv i) (qa i) (&457 / &500) (&1)) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&457 / &500) (&2) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&113 / &50) /\
    linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&1) (&64 / &25) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&33 / &20) (&47 / &20) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&8 / &5) (&3) /\
    linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&87 / &50) (&3) /\
    linside (qc 3) (qs 3) (qu 3) (qv 3) (qa 3) (&1) (&3)`;;

let C1089LSE_APART2 = prove
 (`forall qc qs qu qv qa i j.
     oc1089lssj_base qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> forall x y. ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
                 linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)`,
  REWRITE_TAC[oc1089lssj_base] THEN MESON_TAC[]);;

let C1089LSE_APART3 = prove
 (`forall qc qs qu qv qa i j x y.
     oc1089lssj_base qc qs qu qv qa /\ i < 12 /\ j < 12 /\ ~(i = j)
     ==> ~(linside (qc i) (qs i) (qu i) (qv i) (qa i) x y /\
           linside (qc j) (qs j) (qu j) (qv j) (qa j) x y)`,
  REWRITE_TAC[oc1089lssj_base] THEN MESON_TAC[]);;

(* the chart A = (pullY r).translated 2 2 *)
let C1089LSE_ACHART = prove
 (`forall c s u v a x y.
     linside c (--s) (u - &2 * c - &2 * s) (&2 * c - &2 * s - v - a) a x y <=>
     linside c s u v a (&2 + x) (&2 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* unfold input and base into assumptions; unit normals and sides of the
   listed squares *)
let C1089LSE_SETUP_TAC idx =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[c1089lse_input] o check (fun th ->
    fst(strip_comb(concl th)) = `c1089lse_input`)) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = `(qa:num->real) 4 = qa 7` then
    STRIP_ASSUME_TAC(MATCH_MP (REAL_ARITH `x:real = y ==> x <= y /\ y <= x`) th) else NO_TAC) THEN
  FIRST_ASSUM(MP_TAC o REWRITE_RULE[oc1089lssj_base] o check (fun th ->
    fst(strip_comb(concl th)) = `oc1089lssj_base`)) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  (fun (asl,w as g) ->
    let ths = filter (fun th -> match strip_forall(concl th) with
      | ([v], t) -> is_imp t && lhand t = mk_binop `(<):num->num->bool` v `12`
      | _ -> false) (map snd asl) in
    MAP_EVERY (fun i ->
      let n = mk_small_numeral i in
      let lt = EQT_ELIM(NUM_REDUCE_CONV(mk_binop `(<):num->num->bool` n `12`)) in
      MAP_EVERY (fun th -> ASSUME_TAC(MP (SPEC n th) lt)) ths) idx g);;

let C1089LSE_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
           FIRST_ASSUM ACCEPT_TAC;
         CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
         FIRST (map (fun j ->
           MATCH_MP_TAC OC1089LSSJ_APART THEN EXISTS_TAC j THEN
           ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN NO_TAC)
           [`0`; `3`; `4`; `6`; `7`; `8`; `11`]);
         REPEAT GEN_TAC THEN MATCH_MP_TAC C1089LSE_APART3 THEN ASM_REWRITE_TAC[] THEN
           CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         RASM_ARITH_TAC];;

let C1089LSE_APPLY_TAC th tuple charts =
  let th1 = CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (REWRITE_RULE(charts @ [REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]) (SPECL tuple th)) in
  MP_TAC(if is_neg(concl th1) then NOT_ELIM th1 else th1) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089LSE_SIDE_TAC; DISCH_TAC] THEN
  TRY(FIRST_ASSUM CONTR_TAC);;

(* Lean: southwest_crosspoint_and_left_omission *)
let C1089LSE_SOUTHWEST_CROSSPOINT_AND_LEFT_OMISSION = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lse_input qc qs qu qv qa
     ==> linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&3 / &2) (&2) /\
         ~linside (qc 8) (qs 8) (qu 8) (qv 8) (qa 8) (&87 / &50) (&2)`,
  C1089LSE_SETUP_TAC [4; 0; 8] THEN
  MP_TAC(SPECL [`qc 4:real`; `qs 4:real`; `qu 4:real`; `qv 4:real`; `qa 4:real`;
                `qc 0:real`; `qs 0:real`; `qu 0:real`; `qv 0:real`; `qa 0:real`;
                `qc 8:real`; `qs 8:real`; `qu 8:real`; `qv 8:real`; `qa 8:real`]
    OBCM_SOUTHWEST_POINT_AND_LEFT_OMISSION) THEN
  DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ldisj] THEN
  REPEAT CONJ_TAC THEN C1089LSE_SIDE_TAC);;

(* Lean: southwest_extra *)
let C1089LSE_SOUTHWEST_EXTRA = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lse_input qc qs qu qv qa
     ==> linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&87 / &50) (&2)`,
  C1089LSE_SETUP_TAC [4; 7; 0; 8] THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  (* the absent marker of Q4 and the singleton bar *)
  SUBGOAL_THEN `~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&457 / &500) (&1)`
    ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `&457 / &500`)) (concl th)
      then MATCH_MP_TAC th THEN CONV_TAC NUM_REDUCE_CONV else NO_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `forall z. &113 / &50 <= z ==> z <= &14 / &5
                    ==> ~linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&4 - z) (&1)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`qc 0:real`; `qs 0:real`; `qu 0:real`; `qv 0:real`; `qa 0:real`;
                  `&28 / &25`; `&1`; `&87 / &50`; `&1`;
                  `(&50 / &31) * ((&4 - z) - &28 / &25)`] CES_INSIDE_SEGMENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `(&1 - &50 / &31 * (&4 - z - &28 / &25)) * &28 / &25 +
      (&50 / &31 * (&4 - z - &28 / &25)) * &87 / &50 = &4 - z /\
      (&1 - &50 / &31 * (&4 - z - &28 / &25)) * &1 +
      (&50 / &31 * (&4 - z - &28 / &25)) * &1 = &1`
      (fun th -> REWRITE_TAC[th]) THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                  `qa:num->real`; `4`; `0`; `&4 - z`; `&1`] OC1089LSSJ_APART) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  (* the outward frame r of rotated *)
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
   (REWRITE_RULE[C1089LSNI_CHART; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG]
   (SPECL [`--(qc 4):real`; `--(qs 4):real`; `qu 4 - &4 * qc 4 - &4 * qs 4`;
           `qv 4 + &4 * qs 4 - &4 * qc 4`; `qa 4:real`] OCOBF_FRAME_ORIGINAL))) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1089LSE_SIDE_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real` (X_CHOOSE_THEN `s1:real` (X_CHOOSE_THEN `u1:real`
    (X_CHOOSE_THEN `v1:real` (X_CHOOSE_THEN `a1:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1 = (qa:num->real) 4`)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[ocobp_faces] o check (fun th ->
    fst(strip_comb(concl th)) = `ocobp_faces`)) THEN
  FIRST_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `c1:real`)) (concl th) then
      ASSUME_TAC(GEN_ALL(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (SPEC_ALL th)))
    else NO_TAC) THEN
  (* rSharp *)
  C1089LSE_APPLY_TAC OCOBP_POSITIVE_POINT_ORIGINAL
    [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `qa 4:real`]
    [ASSUME `forall x y. linside c1 s1 u1 v1 (qa 4) x y <=>
                   linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&4 - x) (&4 - y)`] THEN
  (* the half-angle bounds *)
  SUBGOAL_THEN `c1 pow 2 + s1 pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `&143 / &500`] OCSPS_HALF_UPPER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c1:real`; `s1:real`; `&37 / &50`] OCSPS_HALF_LOWER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the leftBar exclusion for N *)
  SUBGOAL_THEN `forall y. &13 / &50 <= y ==> y <= &14 / &25
                    ==> ~linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&1) (&2 + y)`
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`qc 8:real`; `qs 8:real`; `qu 8:real`; `qv 8:real`; `qa 8:real`;
                  `&1`; `&113 / &50`; `&64 / &25`] OCWPVG_VERTICAL_OWNED) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o SPEC `&2 + y`) THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                  `qa:num->real`; `7`; `8`; `&1`; `&2 + y`] OC1089LSSJ_APART) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `forall x y. linside c1 (--s1) (u1 - &2 * c1 - &2 * s1)
                        (&2 * c1 - &2 * s1 - v1 - qa 4) (qa 4) x y <=>
                      linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2 - x) (&2 + y)`
    ASSUME_TAC THENL
   [ASM_REWRITE_TAC[C1089LSE_ACHART] THEN REPEAT GEN_TAC THEN
    REWRITE_TAC[REAL_ARITH `&4 - (&2 + x) = &2 - x /\ &4 - (&2 - y) = &2 + y`];
    ALL_TAC] THEN
  ASM_CASES_TAC `linside (qc 7) (qs 7) (qu 7) (qv 7) (qa 7) (&2) (&113 / &50)` THENL
   [C1089LSE_APPLY_TAC OCOP_IMPOSSIBLE
     [`c1:real`; `--s1:real`; `u1 - &2 * c1 - &2 * s1`; `&2 * c1 - &2 * s1 - v1 - qa 4`;
      `qa 4:real`;
      `--(qc 7):real`; `qs 7:real`; `qu 7 - &2 * qc 7 - &2 * qs 7`;
      `--(qv 7) - qa 7 - &2 * qs 7 + &2 * qc 7`; `qa 7:real`; `s1:real`]
     [ldisj; OBCM_CHART;
      ASSUME `forall x y. linside c1 (--s1) (u1 - &2 * c1 - &2 * s1)
                        (&2 * c1 - &2 * s1 - v1 - qa 4) (qa 4) x y <=>
                      linside (qc 4) (qs 4) (qu 4) (qv 4) (qa 4) (&2 - x) (&2 + y)`];
    ALL_TAC] THEN
  C1089LSE_APPLY_TAC OCUBP_POINT
    [`--(qc 7):real`; `qs 7:real`; `qu 7 - &2 * qc 7 - &2 * qs 7`;
     `--(qv 7) - qa 7 - &2 * qs 7 + &2 * qc 7`; `qa 7:real`] [OBCM_CHART] THEN
  MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                `qa:num->real`; `4`; `7`; `&59 / &40`; `&17 / &8`] OC1089LSSJ_APART) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: impossible *)
let C1089LSE_IMPOSSIBLE = prove
 (`forall qc qs qu qv qa.
     (forall i. i < 12 ==> qc i * qc i + qs i * qs i = &1) /\
     c1089lse_input qc qs qu qv qa
     ==> false`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`;
                `qa:num->real`] OC1089LSSJ_IMPOSSIBLE) THEN
  ASM_SIMP_TAC[oc1089lssj_data; C1089LSE_SOUTHWEST_EXTRA] THEN
  UNDISCH_TAC `c1089lse_input qc qs qu qv qa` THEN SIMP_TAC[c1089lse_input]);;

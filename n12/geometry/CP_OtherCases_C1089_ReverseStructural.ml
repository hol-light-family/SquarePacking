(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/ReverseStructural.lean        *)
(* (namespace N12Compact.Completion.OtherCases.C1089.Reverse).  The five     *)
(* continuous exclusions on the actual C1089 reverse-sector table.           *)
(* q : Fin 12 -> OpenSquare is qc qs qu qv qa : num -> real (i < 12) with   *)
(* the unit normals as the explicit hypothesis                              *)
(*   !i. i < 12 ==> qc i * qc i + qs i * qs i = &1;                          *)
(* PointTable q is c1089rp_point_table (ReversePrefix.ml).  pullX / pullY /  *)
(* pullSwap are the tuples of WallCore.ml (LINSIDE_PULLX / Y / SW);          *)
(* q.translated 2 2 is (c, s, u - (c * &2 + s * &2), v - (--s * &2 + c * &2),*)
(* a).  OutwardBarPoint.point_original / Faces = OCOBP_POINT_ORIGINAL /      *)
(* ocobp_faces, OutwardBarFrame.frame_original = OCOBF_FRAME_ORIGINAL,       *)
(* UpperBarPoint.point_original = OCUBP_POINT_ORIGINAL, ElbowPoint.          *)
(* points_original = OCEP_POINTS_ORIGINAL, CrossedElbow.impossible_original /*)
(* point_original = OCCE_IMPOSSIBLE_ORIGINAL / OCCE_POINT_ORIGINAL,          *)
(* OutwardPair.impossible = OCOP_IMPOSSIBLE, half = C1092WPS_half,           *)
(* SharpPointScalars.half_upper / half_lower = OCSPS_HALF_UPPER / _LOWER,    *)
(* C1090.Residual.Input / impossible = c1090ro_input / C1090RE_IMPOSSIBLE.   *)
(* (Lean header: "source translation only".)  Tag C1089RS_.                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_ReversePrefix.ml";;
needs "n12/geometry/CP_OtherCases_C1090_ResidualEnding.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarFrame.ml";;
needs "n12/geometry/CP_OtherCases_OutwardPair.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_CrossedElbow.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;

let C1089RS_Q = [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;
let C1089RS_UNIT = `forall i. i < 12 ==> (qc:num->real) i * qc i + (qs:num->real) i * qs i = &1`;;
let C1089RS_PT = list_mk_comb(`c1089rp_point_table`, C1089RS_Q);;
let c1089rs_stmt hyps concl =
  list_mk_forall(C1089RS_Q, mk_imp(list_mk_conj([C1089RS_UNIT; C1089RS_PT] @ hyps), concl));;
let c1089rs_sq i = map (fun f -> mk_comb(f, mk_small_numeral i)) C1089RS_Q;;
let c1089rs_own i x y = list_mk_comb(`linside`, c1089rs_sq i @ [x; y]);;

(* unfold the table into assumptions; concrete unit normals and sides *)
let C1089RS_START_TAC idx =
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if concl th = C1089RS_PT then
    MAP_EVERY ASSUME_TAC (CONJUNCTS (REWRITE_RULE[c1089rp_point_table; c1089od_frame] th))
    else NO_TAC) THEN
  MAP_EVERY (fun i ->
    let n = mk_small_numeral i in
    let lt = ARITH_RULE (mk_binop `(<):num->num->bool` n `12`) in
    FIRST_ASSUM(fun th -> if concl th = C1089RS_UNIT then ASSUME_TAC (MP (SPEC n th) lt) else NO_TAC) THEN
    FIRST_ASSUM(fun th -> let t = concl th in
      if is_forall t && can (term_match [] `forall i. i < 12 ==> &1 < (qa:num->real) i`) t
      then ASSUME_TAC (MP (SPEC n th) lt) else NO_TAC)) idx;;

(* the apart field at literal indices i, j *)
let c1089rs_apart_tac i j ttac (asl, w as g) =
  let ap = find (fun th -> let t = concl th in is_forall t &&
                   can (find_term ((=) `~(i:num = j)`)) t) (map snd asl) in
  let ni = mk_small_numeral i and nj = mk_small_numeral j in
  let cond = ARITH_RULE (list_mk_conj [mk_binop `(<):num->num->bool` ni `12`;
                                       mk_binop `(<):num->num->bool` nj `12`;
                                       mk_neg (mk_eq(ni, nj))]) in
  ttac (MP (SPECL [ni; nj] ap) cond) g;;

(* contradiction from two distinct q i containing the same point *)
let C1089RS_CLASH_TAC (asl, w as g) =
  let owned = List.filter_map (fun (_, th) ->
     let t = concl th in
     try let f, args = strip_comb t in
         if f <> `linside` then failwith "" else
         let h = hd args in
         if rator h <> `qc:num->real` then failwith "" else
         Some (dest_small_numeral (rand h), (el 5 args, el 6 args))
     with _ -> None) asl in
  let pairs = flat (map (fun (m, p) -> List.filter_map (fun (n, q) ->
     if m < n && aconv (fst p) (fst q) && aconv (snd p) (snd q) then Some (m, n, p) else None) owned)
     owned) in
  if pairs = [] then failwith "C1089RS_CLASH_TAC" else
  let (m, n, (x, y)) = hd pairs in
  c1089rs_apart_tac m n (fun th -> MP_TAC (SPECL [x; y] th) THEN ASM_REWRITE_TAC[]) g;;

let C1089RS_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C1089RS_CLASH_TAC;
         FIRST_ASSUM(fun th -> if is_disj (concl th) then MP_TAC th THEN CONV_TAC TAUT else NO_TAC);
         RASM_ARITH_TAC];;

let C1089RS_APPLY_TAC th =
  MP_TAC th THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN C1089RS_SIDE_TAC; CONV_TAC TAUT];;
let C1089RS_REFUTE_TAC th =
  MATCH_MP_TAC (if is_neg (concl th) then NOT_ELIM th else th) THEN
  REPEAT CONJ_TAC THEN C1089RS_SIDE_TAC;;
let C1089RS_HAVE_TAC tm tac = SUBGOAL_THEN tm ASSUME_TAC THENL [tac; ALL_TAC];;

(* a bar of q j excludes the parallel bar of q i *)
let C1089RS_BAR_TAC i j pt =
  REPEAT STRIP_TAC THEN
  c1089rs_apart_tac i j (fun th -> MP_TAC (SPECL pt th)) THEN ASM_SIMP_TAC[];;

let c1089rs_bottom_bar_tm =
  mk_forall(`z:real`, mk_imp(`&113 / &50 <= z`, mk_imp(`z <= &14 / &5`,
    mk_neg (c1089rs_own 5 `z:real` `&1`))));;
let c1089rs_right_bar_tm =
  mk_forall(`y:real`, mk_imp(`&113 / &50 <= y`, mk_imp(`y <= &64 / &25`,
    mk_neg (c1089rs_own 6 `&3` `y:real`))));;

(* Lean: northeast_f5_or_f7 *)
let C1089RS_NORTHEAST_F5_OR_F7 = prove
 (c1089rs_stmt [] (mk_disj(c1089rs_own 6 `&2` `&113 / &50`, c1089rs_own 6 `&12 / &5` `&3`)),
  C1089RS_START_TAC [] THEN
  FIRST_X_ASSUM(fun th -> if is_disj (concl th) && length (disjuncts (concl th)) = 3
    then DISJ_CASES_THEN2 (fun t -> REWRITE_TAC[t]) (DISJ_CASES_THEN2 (fun t -> REWRITE_TAC[t])
           ASSUME_TAC) th
    else NO_TAC) THEN
  C1089RS_CLASH_TAC);;

(* Lean: southeast_outward_point *)
let C1089RS_SOUTHEAST_OUTWARD_POINT = prove
 (c1089rs_stmt [mk_neg (c1089rs_own 5 `&113 / &50` `&2`)] (c1089rs_own 5 `&101 / &40` `&17 / &8`),
  C1089RS_START_TAC [5] THEN
  C1089RS_HAVE_TAC c1089rs_bottom_bar_tm (C1089RS_BAR_TAC 5 9 [`z:real`; `&1`]) THEN
  C1089RS_APPLY_TAC (c1089wc_inst OCOBP_POINT_ORIGINAL (c1089wc_py (c1089rs_sq 5))));;

(* Lean: southeast_outward_frame *)
let C1089RS_SOUTHEAST_OUTWARD_FRAME =
  let py = c1089wc_py (c1089rs_sq 5) in
  let fr = SPECL py OCOBF_FRAME_ORIGINAL in
  prove
   (c1089rs_stmt [mk_neg (c1089rs_own 5 `&113 / &50` `&2`)] (rand (concl fr)),
    C1089RS_START_TAC [5] THEN
    C1089RS_HAVE_TAC c1089rs_bottom_bar_tm (C1089RS_BAR_TAC 5 9 [`z:real`; `&1`]) THEN
    MATCH_MP_TAC fr THEN CONV_TAC C1089WC_PULL_CONV THEN REPEAT CONJ_TAC THEN C1089RS_SIDE_TAC);;

(* Lean: northeast_upper_point *)
let C1089RS_NORTHEAST_UPPER_POINT = prove
 (c1089rs_stmt [c1089rs_own 6 `&12 / &5` `&3`; mk_neg (c1089rs_own 6 `&2` `&113 / &50`)]
    (c1089rs_own 6 `&101 / &40` `&17 / &8`),
  C1089RS_START_TAC [6] THEN
  C1089RS_HAVE_TAC c1089rs_right_bar_tm (C1089RS_BAR_TAC 6 10 [`&3`; `y:real`]) THEN
  C1089RS_APPLY_TAC (SPECL (c1089rs_sq 6) OCUBP_POINT_ORIGINAL));;

(* Lean: northeast_elbow_points *)
let C1089RS_NORTHEAST_ELBOW_POINTS = prove
 (c1089rs_stmt [c1089rs_own 6 `&2` `&113 / &50`; mk_neg (c1089rs_own 6 `&12 / &5` `&3`)]
    (mk_conj(c1089rs_own 6 `&5 / &2` `&2`, c1089rs_own 6 `&101 / &40` `&17 / &8`)),
  C1089RS_START_TAC [6] THEN
  C1089RS_APPLY_TAC (c1089wc_inst OCEP_POINTS_ORIGINAL (c1089wc_sw (c1089wc_px (c1089rs_sq 6)))));;

(* Lean: northeast_elbow_impossible *)
let C1089RS_NORTHEAST_ELBOW_IMPOSSIBLE = prove
 (c1089rs_stmt [c1089rs_own 6 `&2` `&113 / &50`; mk_neg (c1089rs_own 6 `&12 / &5` `&3`)] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_NORTHEAST_ELBOW_POINTS))) THEN
  ASM_CASES_TAC (c1089rs_own 5 `&113 / &50` `&2`) THENL
   [ALL_TAC;
    MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_SOUTHEAST_OUTWARD_POINT)))] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT DISCH_TAC THEN
  C1089RS_START_TAC [5] THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) then STRIP_ASSUME_TAC th else NO_TAC)) THEN
  FIRST [C1089RS_CLASH_TAC;
         C1089RS_REFUTE_TAC (c1089wc_inst OCCE_IMPOSSIBLE_ORIGINAL (c1089rs_sq 5 @ [`&4 / &5`]))]);;

(* Lean: northeast_upper_g6_impossible *)
let C1089RS_NORTHEAST_UPPER_G6_IMPOSSIBLE = prove
 (c1089rs_stmt [c1089rs_own 6 `&12 / &5` `&3`; c1089rs_own 6 `&113 / &50` `&2`;
                mk_neg (c1089rs_own 6 `&2` `&113 / &50`)] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_NORTHEAST_UPPER_POINT))) THEN
  SUBGOAL_THEN (mk_neg (c1089rs_own 5 `&113 / &50` `&2`)) ASSUME_TAC THENL
   [DISCH_TAC THEN C1089RS_START_TAC [] THEN C1089RS_CLASH_TAC; ALL_TAC] THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_SOUTHEAST_OUTWARD_POINT))) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT DISCH_TAC THEN
  C1089RS_START_TAC [] THEN C1089RS_CLASH_TAC);;

(* Lean: southeast_f5_impossible *)
let C1089RS_SOUTHEAST_F5_IMPOSSIBLE = prove
 (c1089rs_stmt [c1089rs_own 5 `&113 / &50` `&2`; c1089rs_own 5 `&2` `&113 / &50`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (mk_neg (c1089rs_own 6 `&2` `&113 / &50`)) ASSUME_TAC THENL
   [DISCH_TAC THEN C1089RS_START_TAC [] THEN C1089RS_CLASH_TAC; ALL_TAC] THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_NORTHEAST_F5_OR_F7))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_NORTHEAST_UPPER_POINT))) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT DISCH_TAC THEN
  C1089RS_START_TAC [5] THEN
  C1089RS_HAVE_TAC (c1089rs_own 5 `&101 / &40` `&17 / &8`)
    (C1089RS_APPLY_TAC (SPECL (c1089rs_sq 5) OCCE_POINT_ORIGINAL)) THEN
  C1089RS_CLASH_TAC);;

(* Lean: outward_top_only_impossible *)
let C1089RS_OUTWARD_TOP_ONLY_IMPOSSIBLE = prove
 (c1089rs_stmt [mk_neg (c1089rs_own 5 `&113 / &50` `&2`); c1089rs_own 6 `&12 / &5` `&3`;
                mk_neg (c1089rs_own 6 `&2` `&113 / &50`)] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_NORTHEAST_UPPER_POINT))) THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_SOUTHEAST_OUTWARD_POINT))) THEN
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT DISCH_TAC THEN
  C1089RS_START_TAC [] THEN C1089RS_CLASH_TAC);;

(* translated (pullY r) 2 2, normalised; translated q 2 2 *)
let C1089RS_A_INSIDE = prove
 (`forall c s u v a x y.
     linside c (--s) (u - &2 * c - &2 * s) (&2 * c - &2 * s - v - a) a x y <=>
     linside c s u v a (&2 + x) (&2 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C1089RS_N_INSIDE = prove
 (`forall c s u v a x y.
     linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a x y <=>
     linside c s u v a (&2 + x) (&2 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1089RS_SAME_TAC i j =
  FIRST_ASSUM(fun th -> let t = concl th in
    if is_forall t && can (term_match [] `forall i j. i < 12 /\ j < 12 ==> (qa:num->real) i = qa j`) t
    then ASSUME_TAC (MP (SPECL [mk_small_numeral i; mk_small_numeral j] th)
                        (ARITH_RULE (list_mk_conj [mk_binop `(<):num->num->bool` (mk_small_numeral i) `12`;
                                                   mk_binop `(<):num->num->bool` (mk_small_numeral j) `12`])))
    else NO_TAC);;

let C1089RS_AEQ =
  mk_forall(`x:real`, mk_forall(`y:real`, mk_eq(
    `linside rc (--rs) (ru - &2 * rc - &2 * rs) (&2 * rc - &2 * rs - rv - ra) ra x y`,
    c1089rs_own 5 `&2 + x` `&2 + y`)));;

(* Lean: outward_mixed_impossible *)
let C1089RS_OUTWARD_MIXED_IMPOSSIBLE = prove
 (c1089rs_stmt [mk_neg (c1089rs_own 5 `&113 / &50` `&2`); c1089rs_own 6 `&2` `&113 / &50`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_SOUTHEAST_OUTWARD_POINT))) THEN
  MP_TAC (UNDISCH_ALL (SPEC_ALL (REWRITE_RULE[IMP_CONJ] C1089RS_SOUTHEAST_OUTWARD_FRAME))) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`rc:real`; `rs:real`; `ru:real`; `rv:real`; `ra:real`] THEN
  REWRITE_TAC[ocobp_faces] THEN STRIP_TAC THEN DISCH_TAC THEN
  REPEAT (POP_ASSUM MP_TAC) THEN REPEAT DISCH_TAC THEN
  C1089RS_START_TAC [5; 6] THEN C1089RS_SAME_TAC 5 6 THEN
  SUBGOAL_THEN `rc pow 2 + rs pow 2 = &1` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_POW_2] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC (SPECL [`rc:real`; `rs:real`; `&143 / &500`] OCSPS_HALF_UPPER) THEN
  MP_TAC (SPECL [`rc:real`; `rs:real`; `&37 / &50`] OCSPS_HALF_LOWER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  (* A = translated (pullY r) 2 2, through the frame equivalence and pullY *)
  C1089RS_HAVE_TAC C1089RS_AEQ
   (REPEAT GEN_TAC THEN REWRITE_TAC[C1089RS_A_INSIDE] THEN
    FIRST_ASSUM(fun th -> if is_forall (concl th) && free_in `ru:real` (concl th)
                          then REWRITE_TAC[th] else NO_TAC) THEN
    REWRITE_TAC[LINSIDE_PULLY; REAL_ARITH `&4 - (&2 - y) = &2 + y`]) THEN
  let inst = SPECL [`rc:real`; `--rs`; `ru - &2 * rc - &2 * rs`; `&2 * rc - &2 * rs - rv - ra`; `ra:real`;
                    `(qc:num->real) 6`; `(qs:num->real) 6`;
                    `(qu:num->real) 6 - ((qc:num->real) 6 * &2 + (qs:num->real) 6 * &2)`;
                    `(qv:num->real) 6 - (--(qs:num->real) 6 * &2 + (qc:num->real) 6 * &2)`;
                    `(qa:num->real) 6`; `rs:real`] OCOP_IMPOSSIBLE in
  let inst' = CONV_RULE (ONCE_DEPTH_CONV (REWR_CONV ldisj) THENC
                         REWRITE_CONV[ASSUME C1089RS_AEQ; C1089RS_N_INSIDE] THENC
                         ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) inst in
  MATCH_MP_TAC (NOT_ELIM inst') THEN REPEAT CONJ_TAC THEN
  FIRST [REPEAT GEN_TAC THEN c1089rs_apart_tac 5 6 (fun th -> ACCEPT_TAC (SPECL [`&2 + x`; `&2 + y`] th));
         C1089RS_SIDE_TAC]);;

(* Lean: southeast_g6 *)
let C1089RS_SOUTHEAST_G6 = prove
 (c1089rs_stmt [] (c1089rs_own 5 `&113 / &50` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  ASM_CASES_TAC (c1089rs_own 6 `&2` `&113 / &50`) THENL
   [MP_TAC (SPEC_ALL C1089RS_OUTWARD_MIXED_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
    MP_TAC (SPEC_ALL C1089RS_NORTHEAST_F5_OR_F7) THEN
    MP_TAC (SPEC_ALL C1089RS_OUTWARD_TOP_ONLY_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]]);;

(* Lean: northeast_f7 *)
let C1089RS_NORTHEAST_F7 = prove
 (c1089rs_stmt [] (c1089rs_own 6 `&12 / &5` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REFUTE_THEN ASSUME_TAC THEN
  MP_TAC (SPEC_ALL C1089RS_NORTHEAST_F5_OR_F7) THEN
  MP_TAC (SPEC_ALL C1089RS_NORTHEAST_ELBOW_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* Lean: central_points *)
let C1089RS_CENTRAL_POINTS = prove
 (c1089rs_stmt []
    (list_mk_conj [c1089rs_own 5 `&113 / &50` `&2`; c1089rs_own 6 `&12 / &5` `&3`;
                   mk_neg (c1089rs_own 5 `&2` `&113 / &50`); mk_neg (c1089rs_own 6 `&113 / &50` `&2`)]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C1089RS_SOUTHEAST_G6) THEN MP_TAC (SPEC_ALL C1089RS_NORTHEAST_F7) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN MP_TAC (SPEC_ALL C1089RS_SOUTHEAST_F5_IMPOSSIBLE) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN C1089RS_START_TAC [] THEN C1089RS_CLASH_TAC]);;

(* Lean: residual_input *)
let C1089RS_RESIDUAL_INPUT = prove
 (c1089rs_stmt [c1089rs_own 5 `&113 / &50` `&2`; c1089rs_own 6 `&12 / &5` `&3`]
    (list_mk_comb(`c1090ro_input`, C1089RS_Q)),
  C1089RS_START_TAC [] THEN REWRITE_TAC[c1090ro_input] THEN REPEAT CONJ_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* Lean: impossible *)
let C1089RS_IMPOSSIBLE = prove
 (c1089wc_stmt []
    [mk_binop `(<=):real->real->bool` (c1089wc_lcy 4096) `&2`;
     mk_binop `(<=):real->real->bool` (c1089wc_lcx 32768) `&2`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  let unit_tm = vsubst (zip c1089od_owners C1089RS_Q) C1089RS_UNIT in
  SUBGOAL_THEN unit_tm ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC OO_UNIT THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC (SPEC_ALL C1089RP_POINT_TABLE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  let hq th = SPECL c1089od_owners th in
  MATCH_MP_TAC (hq C1090RE_IMPOSSIBLE) THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MATCH_MP_TAC (hq C1089RS_RESIDUAL_INPUT) THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC (hq C1089RS_SOUTHEAST_G6) THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
         MATCH_MP_TAC (hq C1089RS_NORTHEAST_F7) THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

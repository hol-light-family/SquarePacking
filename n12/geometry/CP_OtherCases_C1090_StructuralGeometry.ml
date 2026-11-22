(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/StructuralGeometry.lean      *)
(* (namespace N12Compact.Completion.OtherCases.C1090.Structural; Lean header:*)
(* "source translation only, not a compilation").  The five continuous       *)
(* exclusions of C1090-SIMPLIFIED-PROOF section 7.  q : Fin 12 -> OpenSquare *)
(* as in EarlyGeometry.ml (qc qs qu qv qa, unit normals as the hypothesis    *)
(* !i. i < 12 ==> qc i * qc i + qs i * qs i = &1); Early.PointTable q =      *)
(* c1090es_pointTable.  OutwardBarPoint.point_original: OCOBP_POINT_ORIGINAL;*)
(* OutwardBarFrame.frame_original: OCOBF_FRAME_ORIGINAL (the frame r is      *)
(* cr sr ur vr ar; its unit normal and positive side, implicit in Lean's     *)
(* OpenSquare, are stated explicitly); Faces = ocobp_faces;                  *)
(* UpperBarPoint.point_original: OCUBP_POINT_ORIGINAL; ElbowPoint.           *)
(* points_original: OCEP_POINTS_ORIGINAL; CrossedElbow.impossible_original / *)
(* point_original: OCCE_*; SharpPointScalars.half_upper / half_lower:        *)
(* OCSPS_HALF_*; half: C1092WPS_half; OutwardPair.impossible:                *)
(* OCOP_IMPOSSIBLE.  h.apart = C1090EG_FOREIGN.  Tag C1090SG_.               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C1090_EarlySelection.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarFrame.ml";;
needs "n12/geometry/CP_OtherCases_OutwardPair.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;
needs "n12/geometry/CP_OtherCases_CrossedElbow.ml";;
needs "n12/geometry/CP_OtherCases_ElbowPoint.ml";;

let C1090SG_VARS = [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`];;

let c1090sg_stmt hyps concl =
  list_mk_forall(C1090SG_VARS,
    mk_imp(list_mk_conj([C1090EG_UNIT; `c1090es_pointTable qc qs qu qv qa`] @ hyps), concl));;

let c1090sg_in i x y = list_mk_comb(`linside`, c1090eg_q i @ [x; y]);;

(* assumptions: the point table, the input, and the square facts of q i *)
let C1090SG_START_TAC is =
  REPEAT GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN
  FIRST_ASSUM(MAP_EVERY ASSUME_TAC o CONJUNCTS o REWRITE_RULE[c1090es_pointTable] o
    check (can (term_match [] `c1090es_pointTable qc qs qu qv qa`) o concl)) THEN
  MAP_EVERY C1090EG_SQUARE_TAC is THEN C1090EG_UNFOLD_TAC;;

(* ~linside (q i) x y from a point of q j (assumption, possibly a bar) *)
let C1090SG_FOREIGN_TAC js =
  MATCH_MP_TAC C1090EG_FOREIGN THEN
  FIRST (map (fun j -> EXISTS_TAC (mk_small_numeral j) THEN CONV_TAC NUM_REDUCE_CONV THEN
                       ASM_SIMP_TAC[] THEN NO_TAC) js);;

let C1090SG_SIDE_TAC js =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
         ASM_SIMP_TAC[LCONT_PULLX; LCONT_PULLY; LCONT_PULLSW] THEN NO_TAC;
         C1090SG_FOREIGN_TAC js;
         GEN_TAC THEN DISCH_TAC THEN DISCH_TAC THEN C1090SG_FOREIGN_TAC js];;

let C1090SG_PULL_CONV =
  REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW;
               REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THENC REAL_RAT_REDUCE_CONV;;

(* MP_TAC the lemma th at the tuple tp, its antecedent discharged *)
let C1090SG_USE_TAC th tp js =
  let th1 = SPECL tp th in
  let ant = lhand (concl th1) in
  let eq = C1090SG_PULL_CONV ant in
  SUBGOAL_THEN (rhs (concl eq)) MP_TAC THENL
   [REPEAT CONJ_TAC THEN C1090SG_SIDE_TAC js; ALL_TAC] THEN
  DISCH_THEN (MP_TAC o MP th1 o EQ_MP (SYM eq));;

(* the same, the conclusion (rewritten through the pulls) proves the goal *)
let C1090SG_APPLY_TAC th tp js =
  C1090SG_USE_TAC th tp js THEN CONV_TAC (LAND_CONV C1090SG_PULL_CONV) THEN
  DISCH_THEN (fun th -> FIRST (map ACCEPT_TAC (th :: (try CONJUNCTS th with Failure _ -> []))));;

let C1090SG_NOT_TAC tm js =
  SUBGOAL_THEN (mk_neg tm) ASSUME_TAC THENL [C1090SG_FOREIGN_TAC js; ALL_TAC];;

(* apart of q i and q j at a point owned by both (assumptions) *)
let C1090SG_CLASH_TAC i j x y =
  MP_TAC (SPECL (C1090SG_VARS @ [mk_small_numeral i; mk_small_numeral j; x; y]) C1090EG_FOREIGN) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];;

let C1090SG_USE thl = MAP_EVERY (fun th ->
  MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC) thl;;

(* Lean: northeast_f5_or_f7 *)
let C1090SG_NORTHEAST_F5_OR_F7 = prove
 (c1090sg_stmt [] (mk_disj(c1090sg_in 6 `&2` `&113 / &50`, c1090sg_in 6 `&12 / &5` `&3`)),
  C1090SG_START_TAC [] THEN
  C1090SG_NOT_TAC (c1090sg_in 6 `&3` `&113 / &50`) [10] THEN
  MAP_EVERY (MP_TAC o ASSUME)
   [list_mk_disj [c1090sg_in 6 `&2` `&113 / &50`; c1090sg_in 6 `&12 / &5` `&3`; c1090sg_in 6 `&3` `&113 / &50`];
    mk_neg (c1090sg_in 6 `&3` `&113 / &50`)] THEN CONV_TAC TAUT);;

(* Lean: southeast_outward_point *)
let C1090SG_SOUTHEAST_OUTWARD_POINT = prove
 (c1090sg_stmt [mk_neg (c1090sg_in 5 `&113 / &50` `&2`)] (c1090sg_in 5 `&101 / &40` `&17 / &8`),
  C1090SG_START_TAC [5] THEN
  C1090SG_APPLY_TAC OCOBP_POINT_ORIGINAL (c1090eg_pully (c1090eg_q 5)) [10; 1; 9]);;

(* Lean: southeast_outward_frame *)
let C1090SG_SOUTHEAST_OUTWARD_FRAME = prove
 (c1090sg_stmt [mk_neg (c1090sg_in 5 `&113 / &50` `&2`)]
   `exists cr sr ur vr ar. cr * cr + sr * sr = &1 /\ &0 < ar /\
      &0 < cr /\ &0 <= sr /\ sr <= cr /\ ar = qa 5 /\
      (forall x y. linside cr sr ur vr ar x y <=>
             linside (qc 5) (--(qs 5)) (qu 5 - &4 * qs 5) (&4 * qc 5 - qv 5 - qa 5) (qa 5) x y) /\
      ocobp_faces cr sr (ur - (cr * &2 + sr * &2)) (vr - (--sr * &2 + cr * &2)) ar`,
  C1090SG_START_TAC [5] THEN
  C1090SG_USE_TAC OCOBF_FRAME_ORIGINAL (c1090eg_pully (c1090eg_q 5)) [10; 1; 9] THEN
  DISCH_THEN ACCEPT_TAC);;

(* Lean: northeast_upper_point *)
let C1090SG_NORTHEAST_UPPER_POINT = prove
 (c1090sg_stmt [c1090sg_in 6 `&12 / &5` `&3`; mk_neg (c1090sg_in 6 `&2` `&113 / &50`)]
   (c1090sg_in 6 `&101 / &40` `&17 / &8`),
  C1090SG_START_TAC [6] THEN
  C1090SG_APPLY_TAC OCUBP_POINT_ORIGINAL (c1090eg_q 6) [11; 2; 10]);;

(* Lean: northeast_elbow_points *)
let C1090SG_NORTHEAST_ELBOW_POINTS = prove
 (c1090sg_stmt [c1090sg_in 6 `&2` `&113 / &50`; mk_neg (c1090sg_in 6 `&12 / &5` `&3`)]
   (mk_conj(c1090sg_in 6 `&5 / &2` `&2`, c1090sg_in 6 `&101 / &40` `&17 / &8`)),
  C1090SG_START_TAC [6] THEN
  C1090SG_USE_TAC OCEP_POINTS_ORIGINAL (c1090eg_pullsw (c1090eg_pullx (c1090eg_q 6))) [7; 11] THEN
  CONV_TAC (LAND_CONV C1090SG_PULL_CONV) THEN REWRITE_TAC[]);;

(* Lean: northeast_elbow_impossible *)
let C1090SG_NORTHEAST_ELBOW_IMPOSSIBLE = prove
 (c1090sg_stmt [c1090sg_in 6 `&2` `&113 / &50`; mk_neg (c1090sg_in 6 `&12 / &5` `&3`)] `false`,
  C1090SG_START_TAC [5] THEN C1090SG_USE [C1090SG_NORTHEAST_ELBOW_POINTS] THEN
  ASM_CASES_TAC (c1090sg_in 5 `&113 / &50` `&2`) THENL
   [C1090SG_USE_TAC OCCE_IMPOSSIBLE_ORIGINAL (c1090eg_q 5 @ [`&4 / &5`]) [6; 4; 9] THEN REWRITE_TAC[];
    C1090SG_USE [C1090SG_SOUTHEAST_OUTWARD_POINT] THEN
    C1090SG_CLASH_TAC 5 6 `&101 / &40` `&17 / &8`]);;

(* Lean: northeast_upper_g6_impossible *)
let C1090SG_NORTHEAST_UPPER_G6_IMPOSSIBLE = prove
 (c1090sg_stmt [c1090sg_in 6 `&12 / &5` `&3`; c1090sg_in 6 `&113 / &50` `&2`;
                mk_neg (c1090sg_in 6 `&2` `&113 / &50`)] `false`,
  C1090SG_START_TAC [] THEN
  C1090SG_NOT_TAC (c1090sg_in 5 `&113 / &50` `&2`) [6] THEN
  C1090SG_USE [C1090SG_SOUTHEAST_OUTWARD_POINT; C1090SG_NORTHEAST_UPPER_POINT] THEN
  C1090SG_CLASH_TAC 5 6 `&101 / &40` `&17 / &8`);;

(* Lean: southeast_f5_impossible *)
let C1090SG_SOUTHEAST_F5_IMPOSSIBLE = prove
 (c1090sg_stmt [c1090sg_in 5 `&113 / &50` `&2`; c1090sg_in 5 `&2` `&113 / &50`] `false`,
  C1090SG_START_TAC [5] THEN
  C1090SG_NOT_TAC (c1090sg_in 6 `&2` `&113 / &50`) [5] THEN
  SUBGOAL_THEN (c1090sg_in 6 `&12 / &5` `&3`) ASSUME_TAC THENL
   [MP_TAC (SPEC_ALL C1090SG_NORTHEAST_F5_OR_F7) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1090SG_USE [C1090SG_NORTHEAST_UPPER_POINT] THEN
  C1090SG_USE_TAC OCCE_POINT_ORIGINAL (c1090eg_q 5) [4] THEN DISCH_TAC THEN
  C1090SG_CLASH_TAC 5 6 `&101 / &40` `&17 / &8`);;

(* Lean: outward_top_only_impossible *)
let C1090SG_OUTWARD_TOP_ONLY_IMPOSSIBLE = prove
 (c1090sg_stmt [mk_neg (c1090sg_in 5 `&113 / &50` `&2`); c1090sg_in 6 `&12 / &5` `&3`;
                mk_neg (c1090sg_in 6 `&2` `&113 / &50`)] `false`,
  C1090SG_START_TAC [] THEN
  C1090SG_USE [C1090SG_SOUTHEAST_OUTWARD_POINT; C1090SG_NORTHEAST_UPPER_POINT] THEN
  C1090SG_CLASH_TAC 5 6 `&101 / &40` `&17 / &8`);;

(* Lean: outward_mixed_impossible *)
let C1090SG_OUTWARD_MIXED_IMPOSSIBLE = prove
 (c1090sg_stmt [mk_neg (c1090sg_in 5 `&113 / &50` `&2`); c1090sg_in 6 `&2` `&113 / &50`] `false`,
  C1090SG_START_TAC [5; 6] THEN
  C1090SG_USE [C1090SG_SOUTHEAST_OUTWARD_POINT] THEN
  MP_TAC (SPEC_ALL C1090SG_SOUTHEAST_OUTWARD_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cr:real` (X_CHOOSE_THEN `sr:real` (X_CHOOSE_THEN `ur:real`
    (X_CHOOSE_THEN `vr:real` (X_CHOOSE_THEN `ar:real` (STRIP_ASSUME_TAC o REWRITE_RULE[ocobp_faces])))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(ar:real) = (qa:num->real) 5`)) THEN
  (* A = (pullY r).translated 2 2 and N = (q 6).translated 2 2 *)
  SUBGOAL_THEN
   `forall x y. linside cr (--sr) ((ur - &4 * sr) - (cr * &2 + --sr * &2))
                  ((&4 * cr - vr - qa 5) - (-- --sr * &2 + cr * &2)) (qa 5) x y <=>
          linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&2 + x) (&2 + y)`
    ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&2 + x`; `&2 - y`] o check (fun th ->
      is_forall(concl th) && is_iff(snd(strip_forall(concl th))))) THEN
    REWRITE_TAC[LINSIDE_PULLY; REAL_ARITH `&4 - (&2 - y) = &2 + y`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `forall x y. linside (qc 6) (qs 6) (qu 6 - (qc 6 * &2 + qs 6 * &2)) (qv 6 - (--qs 6 * &2 + qc 6 * &2))
                  (qa 6) x y <=>
          linside (qc 6) (qs 6) (qu 6) (qv 6) (qa 6) (&2 + x) (&2 + y)`
    ASSUME_TAC THENL
   [REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  (* the half-angle brackets *)
  SUBGOAL_THEN `cr pow 2 + sr pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC (SPECL [`cr:real`; `sr:real`; `&143 / &500`] OCSPS_HALF_UPPER) THEN
  MP_TAC (SPECL [`cr:real`; `sr:real`; `&37 / &50`] OCSPS_HALF_LOWER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPECL (map (fun t -> inst [`:real`, aty] t)
                [`cr:real`; `--(sr:real)`; `(ur - &4 * sr) - (cr * &2 + --sr * &2):real`;
                 `(&4 * cr - vr - (qa:num->real) 5) - (-- --sr * &2 + cr * &2)`; `(qa:num->real) 5`;
                 `(qc:num->real) 6`; `(qs:num->real) 6`;
                 `(qu:num->real) 6 - (qc 6 * &2 + qs 6 * &2)`; `(qv:num->real) 6 - (--qs 6 * &2 + qc 6 * &2)`;
                 `(qa:num->real) 6`; `sr:real`]) OCOP_IMPOSSIBLE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ldisj] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN NO_TAC;
         MATCH_MP_TAC (SPECL C1090SG_VARS C1090ES_SAME) THEN ASM_REWRITE_TAC[] THEN
         CONV_TAC NUM_REDUCE_CONV THEN NO_TAC;
         RASM_ARITH_TAC;
         C1090SG_FOREIGN_TAC [7; 11; 2];
         REPEAT GEN_TAC THEN REWRITE_TAC[TAUT `~(p /\ q) <=> q ==> ~p`] THEN DISCH_TAC THEN
         C1090SG_FOREIGN_TAC [6]]);;

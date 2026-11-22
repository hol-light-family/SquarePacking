(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C976MergedLeft/LowerFaces.lean      *)
(* (N12Compact.Completion.OtherCases.C976MergedLeft).  Section 4: both       *)
(* lower-face alternatives at the left segment.  Square q is c s u v a       *)
(* (unit normal and positive side explicit); Input / Profile:                *)
(* occ976ml_input / occ976ml_profile; cosine_small / half_small_of_cosine /  *)
(* lower_corner_margin / early_span: OCC976MLS_*; SegmentCorner.             *)
(* crossing_order: SEGC_CROSSING_ORDER; half: C1092WPS_half.  The local      *)
(* alpha, beta, uS, vS, uL, vL are written out.  Tag OCC976MLLF_.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C976MergedLeft_Profile.ml";;

(* Lean: left_lower_face *)
let OCC976MLLF_LEFT_LOWER_FACE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ occ976ml_input c s u v a /\ occ976ml_profile c s u v a
     ==> --(&13 / &50) * s <= u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[occ976ml_input; occ976ml_profile; linside] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `c pow 2 + s pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC (SPECL [`c:real`; `s:real`] OCC976MLS_COSINE_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  (* the segment point t = 0 is not inside: the face uS <= u *)
  SUBGOAL_THEN `--(&6 / &25) * c - (&13 / &100) * s <= u` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&0` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `&13 / &100`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  (* the segment point t = 1 is not inside: the face vL <= v *)
  SUBGOAL_THEN `--(&13 / &50) * c <= v` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `&1` o check (fun th -> is_forall (concl th) &&
      can (find_term ((=) `&13 / &100`)) (concl th))) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&50 / &63 < c` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (SPECL [`c:real`; `s:real`] OCC976MLS_HALF_SMALL_OF_COSINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  (* corner: crossing order of the segment through the lower-left corner *)
  MP_TAC (SPECL [`u:real`; `u + a`; `--(v + a)`; `--v`;
                 `--(&6 / &25) * c - (&13 / &100) * s`; `--((&6 / &25) * s - (&13 / &100) * c)`;
                 `--(&13 / &50) * s`; `--(--(&13 / &50) * c)`] SEGC_CROSSING_ORDER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [RASM_ARITH_TAC; RASM_ARITH_TAC; RASM_ARITH_TAC; RASM_ARITH_TAC; RASM_ARITH_TAC;
      RASM_ARITH_TAC;
      X_GEN_TAC `t:real` THEN DISCH_TAC THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o (fun th -> MP (MP (SPEC `t:real` th) (ASSUME `&0 <= t`)) (ASSUME `t <= &1`)) o
        check (fun th -> is_forall (concl th) && can (find_term ((=) `&13 / &100`)) (concl th))) THEN
      CONV_TAC(ONCE_DEPTH_CONV(fun t -> if type_of t = `:real` then REAL_POLY_CONV t else failwith "")) THEN
      REAL_ARITH_TAC];
    DISCH_TAC] THEN
  SUBGOAL_THEN `--(&39 / &625) <= ((&13 / &100) * c + (&6 / &25) * s) * u +
                                   ((&6 / &25) * c - (&13 / &100) * s) * v` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(--v - --((&6 / &25) * s - (&13 / &100) * c)) *
       (--(&13 / &50) * s - (--(&6 / &25) * c - (&13 / &100) * s)) <=
       (u - (--(&6 / &25) * c - (&13 / &100) * s)) *
       (--(--(&13 / &50) * c) - --((&6 / &25) * s - (&13 / &100) * c))`;
      `c * c + s * s = &1`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= ((&13 / &100) * c + (&6 / &25) * s) * (((&27 / &100) * c + s) - (u + a)) /\
                &0 <= ((&6 / &25) * c - (&13 / &100) * s) * (c - (v + a))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC (SPECL [`c:real`; `s:real`] OCC976MLS_LOWER_CORNER_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < (a - &1) * ((&37 / &100) * c + (&11 / &100) * s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`--(&39 / &625) <= ((&13 / &100) * c + (&6 / &25) * s) * u +
                       ((&6 / &25) * c - (&13 / &100) * s) * v`;
    `&0 <= ((&13 / &100) * c + (&6 / &25) * s) * (((&27 / &100) * c + s) - (u + a))`;
    `&0 <= ((&6 / &25) * c - (&13 / &100) * s) * (c - (v + a))`;
    `&0 < (&37 / &100) * c + (&11 / &100) * s - &27 / &80 +
          (&351 / &10000) * s pow 2 - (&81 / &1250) * c * s`;
    `&0 < (a - &1) * ((&37 / &100) * c + (&11 / &100) * s)`;
    `c * c + s * s = &1`] THEN
  REAL_ARITH_TAC);;

(* Lean: half_large *)
let OCC976MLLF_HALF_LARGE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ occ976ml_input c s u v a /\ occ976ml_profile c s u v a
     ==> &7 / &20 < C1092WPS_half c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL OCC976MLLF_LEFT_LOWER_FACE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC (SPECL [`c:real`; `s:real`] OCC976MLS_EARLY_SPAN) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[occ976ml_input; occ976ml_profile]) THEN
  REPEAT (FIRST_X_ASSUM (CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl))) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC);;

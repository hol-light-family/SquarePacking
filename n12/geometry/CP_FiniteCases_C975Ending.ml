(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/C975Ending.lean                    *)
(* (namespace N12Compact.FiniteCases.C975Selection; Lean header:            *)
(* "uncompiled").  The complete actual C975 ending: the original family     *)
(* c975d_family is impossible.  Conventions of CP_FiniteCases_C975NortheastSign.ml *)
(* (OpenSquare N = cN sN uN vN aN with unit normal / positive side explicit, *)
(* translated 2 3 = c975ns_tr23).  ClosedFrames.canonical_frame =            *)
(* CLF_CANONICAL_FRAME; negative_top_lower = C975TO_NEGATIVE_TOP_LOWER;      *)
(* C976NegativeTop.faces = CC976F_FACES (Faces = cc976f_faces, its upperU    *)
(* field u + a <= c + 11/25 t); vertical_segment = OO_VERTICAL_SEGMENT.      *)
(* For the assembly: C975EN_EXCLUDES (excl_case 975) and C975EN_EXCLUDED_ROW *)
(* (row 506).  Tag C975EN_.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975NortheastSign.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: mixed_lower_face *)
let C975EN_MIXED_LOWER_FACE = prove
 (`forall cN sN uN vN aN s.
     cN * cN + sN * sN = &1 /\ &0 < aN /\
     sN = --s /\ &0 < cN /\ &0 < s /\
     linside cN sN uN vN aN (&7 / &20) (--(&13 / &20)) /\
     linside cN sN uN vN aN (&0) (--(&37 / &50)) /\
     linside cN sN uN vN aN (&13 / &50) (&0) /\
     ~linside cN sN uN vN aN (&0) (--(&1 / &2))
     ==> (&1 / &2) * s <= uN`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sN = --s`)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cN (--s) uN vN aN (&0) (--(&1 / &2))` THEN REWRITE_TAC[] THEN
  MAP_EVERY (MP_TAC o ASSUME)
    [`linside cN (--s) uN vN aN (&7 / &20) (--(&13 / &20))`;
     `linside cN (--s) uN vN aN (&0) (--(&37 / &50))`;
     `linside cN (--s) uN vN aN (&13 / &50) (&0)`;
     `&0 < cN`; `&0 < s`; `uN < &1 / &2 * s`] THEN
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let C975EN_IMPOSSIBLE =
  let tR = [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `l:real`] in
  let tN = c975ns_tr23 tR in
  let lin q x y = list_mk_comb(`linside`, q @ [x; y]) in
  let frame m nm =
    let th = MP (SPECL (c975ns_owner m) CLF_CANONICAL_FRAME)
                (CONJ (c975cr_unit m) (MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) C975CR_SIDE)) in
    itlist (fun v ttac -> X_CHOOSE_THEN v ttac) (c975ns_sq nm) STRIP_ASSUME_TAC th THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = mk_eq(mk_var("a" ^ nm, `:real`), `l:real`))) in
  prove
   (c975ic_stmt [] `false`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    C975NS_SIDE THEN C975NS_OWNER 1024 THEN C975NS_OWNER 34816 THEN
    SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    C975NS_HAVE C975TO_TOP_ORIGIN THEN
    C975NS_HAVE C975SEL_NORTHEAST_SELECTION THEN
    C975NS_HAVE C975SS_NE_MARKER THEN
    C975NS_HAVE C975IC_RIGHT_HIGH THEN
    frame 1024 "R" THEN
    MP_TAC (SPECL (C975NS_V5 @ tR) C975NS_NORTHEAST_NEGATIVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `--sR <= cR` ASSUME_TAC THENL
     [UNDISCH_TAC `abs sR <= cR` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    frame 34816 "W" THEN
    MP_TAC (SPECL (C975NS_V5 @ tR @ [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `l:real`])
              C975NS_TOP_NEGATIVE_SHALLOW) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC (SPECL (C975NS_V5 @ [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `l:real`])
              C975TO_NEGATIVE_TOP_LOWER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(fun th -> ASSUME_TAC (EQ_MP (SPECL [`&2`; `&5 / &2`]
      (ASSUME (c975ns_iff [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `l:real`] 34816 c975ns_id c975ns_id))) th)) THEN
    SUBGOAL_THEN (list_mk_comb(`cc976f_alternative`, tN)) ASSUME_TAC THENL
     [MATCH_MP_TAC (SPECL (C975NS_V5 @ tN) C975NS_NEGATIVE_ALTERNATIVE) THEN
      ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[C975CP_TRANSLATED];
      ALL_TAC] THEN
    (* the faces of N *)
    MP_TAC (CONV_RULE (REWRITE_CONV[C975CP_TRANSLATED] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
              (SPECL (tN @ [`--sR`]) CC976F_FACES)) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST_ASSUM ACCEPT_TAC;
             REWRITE_TAC[REAL_NEG_NEG] THEN NO_TAC;
             ASM_REWRITE_TAC[] THEN NO_TAC;
             ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C975NS_CLASH_TAC;
             RASM_ARITH_TAC];
      REWRITE_TAC[cc976f_faces] THEN
      DISCH_THEN (ASSUME_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2)] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = list_mk_comb(`cc976f_alternative`, tN))) THEN
    REWRITE_TAC[cc976f_alternative; C975CP_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN STRIP_TAC THENL
     [(* outer *)
      SUBGOAL_THEN (c975ns_own 34816 `&2` `&131 / &50`) ASSUME_TAC THENL
       [MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&5 / &2`; `&3`] THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        C975NS_CLASH_TAC];
      (* mixed *)
      SUBGOAL_THEN (mk_neg (lin tN `&0` `--(&1 / &2)`)) ASSUME_TAC THENL
       [REWRITE_TAC[C975CP_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN DISCH_TAC THEN C975NS_CLASH_TAC;
        ALL_TAC] THEN
      MP_TAC (SPECL (tN @ [`--sR`]) C975EN_MIXED_LOWER_FACE) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN
        FIRST [FIRST_ASSUM ACCEPT_TAC;
               REWRITE_TAC[REAL_NEG_NEG] THEN NO_TAC;
               REWRITE_TAC[C975CP_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
               CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
               RASM_ARITH_TAC];
        DISCH_TAC] THEN
      SUBGOAL_THEN `cR <= &1` ASSUME_TAC THENL
       [UNDISCH_TAC `cR * cR + sR * sR = &1` THEN UNDISCH_TAC `&0 < cR` THEN
        REPEAT DISCH_TAC THEN NLIN_TAC [SPEC `sR:real` REAL_LE_SQUARE];
        ALL_TAC] THEN
      RASM_ARITH_TAC]);;

(* Lean (Completion): the case exclusion, via family_excluded at row 506 *)
let C975EN_EXCLUDES = prove
 (`excl_case 975`,
  REWRITE_TAC[ri_excludes_case_iff 506 `c975d_family`; excl_fam] THEN
  MESON_TAC[C975EN_IMPOSSIBLE]);;

(* for the assembly: |- EXCLUDED_ROW 506 *)
let C975EN_EXCLUDED_ROW = ri_excluded_row 506 C975EN_EXCLUDES;;

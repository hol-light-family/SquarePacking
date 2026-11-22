(* ========================================================================= *)
(* Port of Compact/Bridge/C977SignedEscapeClosure.lean                       *)
(* (N12Compact.C977SignedEscapeClosure).  The original C977 missing-center   *)
(* signed escape is impossible; the remaining whole-case obligation is the   *)
(* center-owned ending.  (Lean header: "Source only, uncompiled".)           *)
(* Conventions of C977PositiveBottomWest.ml / C977Residual.ml.               *)
(* OwnedWestBottomAngle.small_bottom: OWBA_SMALL_BOTTOM;                     *)
(* PositiveWallPositiveLeft.cuts: PWPL_CUTS (pwpl_cuts);                     *)
(* C977NextBottomWall.excludes_of_small_bottom:                              *)
(* C977NBW_EXCLUDES_OF_SMALL_BOTTOM.  Tag C977SEC_.                          *)
(* ========================================================================= *)

needs "n12/geometry/C977Residual.ml";;
needs "n12/geometry/C977NextBottomWall.ml";;
needs "n12/geometry/OwnedWestBottomAngle.ml";;
needs "n12/geometry/PositiveWallPositiveLeft.ml";;

(* Lean: apart (private) is C977CRC_APART *)

let C977SEC_CLOSE_TAC =
  REPEAT CONJ_TAC THEN
  REWRITE_TAC[lcont; ldisj] THEN
  REWRITE_TAC[ASSUME (C977PBW_EQ 0); ASSUME (C977PBW_EQ 5)] THEN
  REWRITE_TAC[GSYM lcont] THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC) ORELSE
   (ASM_REWRITE_TAC[] THEN NO_TAC));;

(* Lean: small_bottom *)
let C977SEC_SMALL_BOTTOM = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l qc qs qu qv qa t. %s /\\ %s /\\
      qs 0 = --t /\\ c977cc_normal (qc 0) t /\\ c977cc_normal (qc 5) (qs 5) /\\
      ~linside %s (&1) (&1) /\\ ~linside %s (&2) (&2)
      ==> t < &1 / &5"
   C977CRE_HYP C977PBW_QHYP (c977cre_sq 0) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C977PBW_Q_TAC 0 THEN C977PBW_Q_TAC 5 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_DATA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  C977WC_FACTS_TAC 0 THEN C977WC_FACTS_TAC 1 THEN C977WC_FACTS_TAC 5 THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `c977av_ordered_owner c1 c2 a b l 0`] C977AN_CODE_ONE_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT; c977mcg_anchors] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  ASSUME_TAC (MP (C977CRC_APART_AT 0 5) (C977PBW_HYPS ())) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "linside %s (&1) (&457 / &500) /\\ ~linside %s (&2) (&457 / &500) /\\
     linside %s (&1) (&8 / &5) /\\ lcont %s"
    (c977cre_sq 0) (c977cre_sq 0) (c977cre_sq 1) (c977cre_sq 0)))
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [C977WC_TO_OO_TAC 0 THEN ACCEPT_TAC(C977WC_INST (oo_seed 1 (`&1`, `&457 / &500`)));
      C977WC_TO_OO_TAC 0 THEN MP_TAC(C977WC_INST (oo_missing 1 13)) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
      C977WC_TO_OO_TAC 1 THEN REWRITE_TAC[oo_aux_point 10] THEN C977WC_DOMAIN_CASES_TAC 1;
      C977WC_TO_OO_TAC 0 THEN ASM_SIMP_TAC[OO_BOX]];
    ALL_TAC] THEN
  (* foreignLow *)
  ASSUME_TAC(REWRITE_RULE[ASSUME (parse_term (Printf.sprintf "linside %s (&1) (&8 / &5)" (c977cre_sq 1)))]
    (SPECL [`&1`; `&8 / &5`] (MP (C977CRC_APART_AT 5 1) (C977PBW_HYPS ())))) THEN
  (* cap *)
  let eq5 = ASSUME (C977PBW_EQ 5) in
  SUBGOAL_THEN `qu 5 + qa 5 <= &2 * (qc 5 + qs 5)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC (parse_term (Printf.sprintf "~linside %s (&2) (&2)" (c977cre_sq 5))) THEN
    REWRITE_TAC[GSYM eq5] THEN
    MP_TAC(ASSUME `c977cc_normal (qc 5) (qs 5)`) THEN
    DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)) THEN
    MAP_EVERY (fun (x, y) ->
      let e = SPECL [x; y] eq5 in
      STRIP_ASSUME_TAC(REWRITE_RULE[linside] (EQ_MP (SYM e) (ASSUME (rand(concl e))))))
     [(`&33 / &20`, `&33 / &20`); (`&2`, `&87 / &50`); (`&87 / &50`, `&2`)] THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  let qO = [`(qc:num->real) 0`; `(qs:num->real) 0`; `(qu:num->real) 0`; `(qv:num->real) 0`; `(qa:num->real) 0`]
  and qA = [`(qc:num->real) 5`; `(qs:num->real) 5`; `(qu:num->real) 5`; `(qv:num->real) 5`; `(qa:num->real) 5`] in
  ASM_CASES_TAC `linside (qc 5) (qs 5) (qu 5) (qv 5) (qa 5) (&1) (&2)` THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[eq5]) THENL
   [MATCH_MP_TAC OWBA_SMALL_BOTTOM THEN MAP_EVERY EXISTS_TAC (qO @ qA) THEN C977SEC_CLOSE_TAC;
    MP_TAC(SPECL (qO @ qA @ [`t:real`]) PWPL_CUTS) THEN
    ANTS_TAC THENL [C977SEC_CLOSE_TAC; SIMP_TAC[pwpl_cuts]]]);;

(* Lean: signed_escape_excludes *)
let C977SEC_SIGNED_ESCAPE_EXCLUDES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ ~linside %s (&1) (&1) /\\ c977res_signed c1 c2 a b l ==> F"
   C977CRE_HYP (c977cre_sq 0)),
  REPEAT GEN_TAC THEN REWRITE_TAC[c977res_signed] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`;
                `--(qs:num->real) 0`] C977SEC_SMALL_BOTTOM) THEN
  C977PBW_Q_TAC 0 THEN C977PBW_Q_TAC 5 THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> &0 < qc i /\ abs (qs i) <= qc i`) (concl th)
    then MP_TAC(CONJ (REWRITE_RULE[ARITH] (SPEC `0` th)) (REWRITE_RULE[ARITH] (SPEC `5` th))) else NO_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `c977cc_normal (qc 0) (--(qs 0)) /\ c977cc_normal (qc 5) (qs 5)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC THEN
  MATCH_MP_TAC C977NBW_EXCLUDES_OF_SMALL_BOTTOM THEN
  MAP_EVERY EXISTS_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
    `(qc:num->real) 0`; `(qs:num->real) 0`; `(qu:num->real) 0`; `(qv:num->real) 0`; `(qa:num->real) 0`;
    `--(qs:num->real) 0`] THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN RASM_ARITH_TAC);;

(* Lean: center_owned *)
let C977SEC_CENTER_OWNED = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ ~linside %s (&1) (&1) ==> linside %s (&2) (&2)"
   C977CRE_HYP (c977cre_sq 0) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C977RES_ALTERNATIVES) THEN ASM_REWRITE_TAC[c977res_alt] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (TAUT `false ==> p`) THEN
  MATCH_MP_TAC (SPEC_ALL C977SEC_SIGNED_ESCAPE_EXCLUDES) THEN ASM_REWRITE_TAC[]);;

(* Lean: excludes_case_of_center_ending *)
let C977SEC_EXCLUDES_CASE_OF_CENTER_ENDING = prove
 (parse_term (Printf.sprintf
   "(!c1 c2 a b l. NPACK c1 c2 a b l /\\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\\
       c977mcp_strengthened %s /\\ c977mcb_ccb %s
       ==> !w. c977wb_owners c1 c2 a b l w /\\
               c977wb_half c1 c2 a b l w (c977wc_expand (F,F)) /\\
               MEM (c977av_actual c1 c2 a b l) c977ow_remaining
               ==> linside %s (&2) (&2) ==> F)
    ==> excl_case 977"
   (c977cre_sq 0) (c977cre_sq 0) (c977cre_sq 5)),
  DISCH_TAC THEN MATCH_MP_TAC C977RES_EXCLUDES_CASE_OF_TWO_ENDINGS THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:num->num`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC (SPEC_ALL C977SEC_SIGNED_ESCAPE_EXCLUDES) THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> fst (strip_comb (concl th)) = `c977mcp_strengthened`)) THEN
    SIMP_TAC[c977mcp_strengthened; c977cr_mce]]);;

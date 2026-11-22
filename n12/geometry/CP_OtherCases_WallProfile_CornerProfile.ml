(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/WallProfile/CornerProfile.lean      *)
(* (Jatloe, N12-jatloe; namespace                                            *)
(*  N12Compact.Completion.OtherCases.WallProfile).                           *)
(* The full corner support profile (Theorem6 of C1092-DIRECT-WALL-POINT).    *)
(* Lean upper is ABT_upper; profile/half are C1092WPS_profile/C1092WPS_half; *)
(* positive_frame is OCWPSG_POSITIVE_FRAME, downward_upper is                *)
(* OCWPSG_DOWNWARD_UPPER, envelope is C1092WPS_ENVELOPE.  The square is      *)
(* cq sq uq vq aq with its OpenSquare invariants as explicit hypotheses; the *)
(* target direction is (c, s).                                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

let OCWPCP_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;
let OCWPCP_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let OCWPCP_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let OCWPCP_NONNEG_OF_MUL = prove
 (`forall k y. &0 < k /\ &0 <= k * y ==> &0 <= y`,
  REPEAT STRIP_TAC THEN NLIN_TAC []);;

let OCWPCP_CANCEL = prove
 (`forall k x y. &0 < k /\ k * x = k * y ==> x = y`,
  MESON_TAC[REAL_EQ_MUL_LCANCEL; REAL_LT_IMP_NZ]);;

(* Lean: kappa_complement (private) *)
let OCWPCP_KAPPA_COMPLEMENT = prove
 (`forall c s. &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
         ==> &1 - (c + s) / (&1 + c) <= c / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c - &1`] [`c <= &1`] THEN
  SUBGOAL_THEN `(&1 + c) * ((c + s) / (&1 + c)) = c + s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_DIV_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `k = (c + s) / (&1 + c)` THEN
  SUBGOAL_THEN `&0 <= c * (&1 + c) - &2 * (&1 - s)` ASSUME_TAC THENL
  [MATCH_MP_TAC OCWPCP_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + s` THEN
   CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `(&1 + s) * (c * (&1 + c) - &2 * (&1 - s)) = c * (&1 - c + s * (&1 + c))`
   SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THENL
   [RASM_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&1 + c) * (c / &2 - (&1 - k))` MP_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `&0 <= c / &2 - (&1 - k)` MP_TAC THENL
  [MATCH_MP_TAC OCWPCP_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + c` THEN
   CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: in_positive_frame (private) *)
let OCWPCP_IN_POSITIVE_FRAME = prove
 (`forall cq sq uq vq aq c s.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ &1 < aq /\ &0 < cq /\ &0 <= sq /\
     (forall x y. linside cq sq uq vq aq x y ==> &0 <= x /\ &0 <= y) /\
     linside cq sq uq vq aq (&1) (&1) /\ ~linside cq sq uq vq aq (&1) (&3 / &2) /\
     &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> aq * C1092WPS_profile c s <= ABT_upper cq sq uq vq aq c (--s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`]
    TSS_POSITIVE_FRAME_WALL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcx; lcy]) THEN
  SUBGOAL_THEN `&0 <= cq * uq - sq * (vq + aq)` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `sq:real`; SQ_NONNEG `cq - &1`; SQ_NONNEG `cq:real`;
                  SQ_NONNEG `sq - &1`] [`cq <= &1`; `sq <= &1`] THEN
  MP_TAC(ASSUME `linside cq sq uq vq aq (&1) (&1)`) THEN REWRITE_TAC[linside] THEN STRIP_TAC THEN
  SUBGOAL_THEN `uq + aq <= cq + (&3 / &2) * sq \/ vq + aq <= --sq + (&3 / &2) * cq`
  ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cq sq uq vq aq (&1) (&3 / &2)` THEN REWRITE_TAC[linside] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `sq = &0` THENL
  [FIRST_X_ASSUM SUBST_ALL_TAC THEN
   SUBGOAL_THEN `cq = &1` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `x <= &1 /\ &1 <= x ==> x = &1`) THEN
    CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
   SUBGOAL_THEN `vq + aq <= &3 / &2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN RASM_ARITH_TAC; ALL_TAC] THEN
   MP_TAC(SPECL [`&1`; `&0`; `uq:real`; `vq:real`; `aq:real`; `c:real`; `s:real`]
     OCWPSG_DOWNWARD_UPPER) THEN
   ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
   MP_TAC(SPECL [`c:real`; `s:real`; `&1`; `&0`] C1092WPS_ENVELOPE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= c ==> max (c * &1 - s * &0) (&0) = c`] THEN
   REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_LZERO; real_div; REAL_MUL_RID] THEN DISCH_TAC THEN
   OCWPCP_PROD_TAC `aq:real` `(c - s / &2) - C1092WPS_profile c s` THEN
   OCWPCP_PROD_TAC `c:real` `uq:real` THEN
   OCWPCP_PROD_TAC `s:real` `&3 / &2 - (vq + aq)` THEN
   OCWPCP_PROD_TAC `(&3 / &2) * s` `aq - &1` THEN
   NLIN_TAC ~deg2:false [];
   ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sq` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
   UNDISCH_TAC `cq * cq + sq * sq = &1` THEN CONV_TAC REAL_RING; STRIP_TAC] THEN
  SUBGOAL_THEN `sq * C1092WPS_half cq sq = &1 - cq` ASSUME_TAC THENL
  [MATCH_MP_TAC OCWPCP_CANCEL THEN
   EXISTS_TAC `&1 + cq` THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `C1092WPS_half cq sq * (&1 + cq) = sq` THEN UNDISCH_TAC `cq * cq + sq * sq = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  OCWPCP_PROD_TAC `c:real` `sq:real` THEN OCWPCP_PROD_TAC `s:real` `cq:real` THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`; `c:real`; `s:real`]
    OCWPSG_DOWNWARD_UPPER) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `cq:real`; `sq:real`] C1092WPS_ENVELOPE) THEN
  ANTS_TAC THENL
  [REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
   UNDISCH_TAC `cq * cq + sq * sq = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `s * sq / (&1 + cq) = s * C1092WPS_half cq sq` SUBST1_TAC THENL
  [REWRITE_TAC[C1092WPS_half; real_div; REAL_MUL_ASSOC]; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= max (c * cq - s * sq) (&0) /\ (c * cq - s * sq) <= max (c * cq - s * sq) (&0)` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `aq * ((c * sq + s * cq) + max (c * cq - s * sq) (&0) + s * C1092WPS_half cq sq - (&3 / &2) * s) <= ((c * cq - s * sq) * uq - (c * sq + s * cq) * vq + aq * max (c * cq - s * sq) (&0)) ==> aq * C1092WPS_profile c s <= ((c * cq - s * sq) * uq - (c * sq + s * cq) * vq + aq * max (c * cq - s * sq) (&0))` ASSUME_TAC THENL
  [DISCH_TAC THEN OCWPCP_PROD_TAC `aq:real` `((c * sq + s * cq) + max (c * cq - s * sq) (&0) + s * C1092WPS_half cq sq - (&3 / &2) * s) - C1092WPS_profile c s` THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   OCWPCP_PROD_TAC `(c * sq + s * cq)` `cq * uq - sq * (vq + aq)` THEN
   OCWPCP_PROD_TAC `s:real` `(cq + (&3 / &2) * sq) - (uq + aq)` THEN
   OCWPCP_PROD_TAC `aq - &1` `s:real` THEN
   OCWPCP_PROD_TAC `(aq - &1) * s` `cq + (&3 / &2) * sq` THEN
   SUBGOAL_THEN
    `sq * (((c * cq - s * sq) * uq - (c * sq + s * cq) * vq + aq * max (c * cq - s * sq) (&0)) - aq * ((c * sq + s * cq) + max (c * cq - s * sq) (&0) + s * C1092WPS_half cq sq - (&3 / &2) * s)) =
     (c * sq + s * cq) * (cq * uq - sq * (vq + aq)) + s * (cq + (&3 / &2) * sq - (uq + aq)) +
     (aq - &1) * s * (cq + (&3 / &2) * sq)` ASSUME_TAC THENL
   [UNDISCH_TAC `sq * C1092WPS_half cq sq = &1 - cq` THEN UNDISCH_TAC `cq * cq + sq * sq = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= ((c * cq - s * sq) * uq - (c * sq + s * cq) * vq + aq * max (c * cq - s * sq) (&0)) - aq * ((c * sq + s * cq) + max (c * cq - s * sq) (&0) + s * C1092WPS_half cq sq - (&3 / &2) * s)` MP_TAC THENL
   [MATCH_MP_TAC OCWPCP_NONNEG_OF_MUL THEN EXISTS_TAC `sq:real` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (c * cq - s * sq)` THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   SUBGOAL_THEN `max (c * cq - s * sq) (&0) = (c * cq - s * sq)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
   OCWPCP_PROD_TAC `(c * cq - s * sq)` `cq * uq - sq * (vq + aq)` THEN
   OCWPCP_PROD_TAC `s:real` `(--sq + (&3 / &2) * cq) - (vq + aq)` THEN
   OCWPCP_PROD_TAC `s:real` `C1092WPS_half cq sq` THEN
   OCWPCP_PROD_TAC `aq - &1` `s:real` THEN
   OCWPCP_PROD_TAC `(aq - &1) * s` `cq:real` THEN
   OCWPCP_PROD_TAC `(aq - &1) * s * cq` `&3 / &2 - C1092WPS_half cq sq` THEN
   SUBGOAL_THEN
    `cq * (((c * cq - s * sq) * uq - (c * sq + s * cq) * vq + aq * (c * cq - s * sq)) - aq * ((c * sq + s * cq) + (c * cq - s * sq) + s * C1092WPS_half cq sq - (&3 / &2) * s)) =
     (c * cq - s * sq) * (cq * uq - sq * (vq + aq)) + s * (--sq + (&3 / &2) * cq - (vq + aq)) +
     s * C1092WPS_half cq sq + (aq - &1) * s * cq * (&3 / &2 - C1092WPS_half cq sq)` ASSUME_TAC THENL
   [UNDISCH_TAC `C1092WPS_half cq sq * (&1 + cq) = sq` THEN UNDISCH_TAC `cq * cq + sq * sq = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= ((c * cq - s * sq) * uq - (c * sq + s * cq) * vq + aq * (c * cq - s * sq)) -
                      aq * ((c * sq + s * cq) + (c * cq - s * sq) + s * C1092WPS_half cq sq - (&3 / &2) * s)` MP_TAC THENL
   [MATCH_MP_TAC OCWPCP_NONNEG_OF_MUL THEN EXISTS_TAC `cq:real` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN `max (c * cq - s * sq) (&0) = &0` SUBST1_TAC THENL
  [REWRITE_TAC[real_max] THEN COND_CASES_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  OCWPCP_PRODLT_TAC `--((c * cq - s * sq))` `(cq + sq) - uq` THEN
  OCWPCP_PROD_TAC `(c * sq + s * cq)` `(--sq + (&3 / &2) * cq) - (vq + aq)` THEN
  SUBGOAL_THEN `(c * cq - s * sq) * (cq + sq) + (c * sq + s * cq) * (sq - (&3 / &2) * cq + aq) = (c - s + (&1 - cq / &2) * (c * sq + s * cq)) + (aq - &1) * (c * sq + s * cq)`
  ASSUME_TAC THENL
  [UNDISCH_TAC `cq * cq + sq * sq = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  OCWPCP_PROD_TAC `cq:real` `s - (c * cq - s * sq)` THEN
  SUBGOAL_THEN `(&1 + sq) * ((c * sq + s * cq) - c) = cq * (s - (c * cq - s * sq))` ASSUME_TAC THENL
  [UNDISCH_TAC `cq * cq + sq * sq = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c <= (c * sq + s * cq)` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (c * sq + s * cq) - c` MP_TAC THENL
   [MATCH_MP_TAC OCWPCP_NONNEG_OF_MUL THEN EXISTS_TAC `&1 + sq` THEN
    CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s - &1`] [`s <= &1`] THEN
  OCWPCP_USE OCWPCP_KAPPA_COMPLEMENT [`c:real`; `s:real`] THEN
  SUBGOAL_THEN `(&1 + c) * ((c + s) / (&1 + c)) = c + s` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_DIV_LMUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_profile c s = c - s * ((c + s) / (&1 + c))` ASSUME_TAC THENL
  [REWRITE_TAC[C1092WPS_profile; real_div; REAL_MUL_ASSOC]; ALL_TAC] THEN
  ABBREV_TAC `kk = (c + s) / (&1 + c)` THEN
  SUBGOAL_THEN `&0 <= kk /\ kk <= &1` STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  OCWPCP_PROD_TAC `&1 - cq / &2` `(c * sq + s * cq) - c` THEN
  OCWPCP_PROD_TAC `&1 - cq` `c:real` THEN
  OCWPCP_PROD_TAC `&1 - s` `&1 - kk` THEN
  OCWPCP_PROD_TAC `s:real` `kk:real` THEN
  OCWPCP_PROD_TAC `aq - &1` `(c * sq + s * cq) - C1092WPS_profile c s` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: corner_profile *)
let OCWPCP_CORNER_PROFILE = prove
 (`forall cq sq uq vq aq c s.
     cq * cq + sq * sq = &1 /\ &0 < aq /\ &1 < aq /\
     (forall x y. linside cq sq uq vq aq x y ==> &0 <= x /\ &0 <= y) /\
     linside cq sq uq vq aq (&1) (&1) /\ ~linside cq sq uq vq aq (&1) (&3 / &2) /\
     &0 <= c /\ &0 <= s /\ c pow 2 + s pow 2 = &1
     ==> aq * C1092WPS_profile c s <= ABT_upper cq sq uq vq aq c (--s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] OCWPSG_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const(fst(strip_comb t))) = "ABT_upper"
                               with Failure _ -> false)) (concl th)
    then REWRITE_TAC[GSYM th] else failwith "") THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a1:real = aq`)) THEN
  MATCH_MP_TAC OCWPCP_IN_POSITIVE_FRAME THEN ASM_REWRITE_TAC[]);;

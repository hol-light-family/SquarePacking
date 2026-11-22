(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TwoFifthsEntranceRight.lean         *)
(* (N12Compact.C1092MMMPTwoFifthsEntrance).  The short bar, the real right   *)
(* wall and the closed MMMP center sign of one actual Q10.  Conventions of   *)
(* CP_C1092_MMMP_TwoFifthsEntranceNortheast.ml and CP_C1092_MMMP_Origins.ml. *)
(* (owners p 10).translated 2 2 is the tuple of CCIP_INSIDE_TRANSLATED:      *)
(* (c, s, u - (c * &2 + s * &2), v - (--s * &2 + c * &2), l).                *)
(* An OpenSquare E is cE sE uE vE aE with its invariants as hypotheses.      *)
(* vertical_segment OO_VERTICAL_SEGMENT, p.contained OO_BOX, side_same: all  *)
(* owners have side l.  Tag C1092MTFER_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_TwoFifthsEntranceNortheast.ml";;

let c1092mtfer_q i f =
  Printf.sprintf "(%s c1 c2 a b l (EL %d c1092wc_code))" f i;;
(* the translated owner i as a string tuple *)
let c1092mtfer_tr i =
  let c = c1092mtfer_q i "ooc" and s = c1092mtfer_q i "oos"
  and u = c1092mtfer_q i "oou" and v = c1092mtfer_q i "oov" in
  Printf.sprintf "%s %s (%s - (%s * &2 + %s * &2)) (%s - (--%s * &2 + %s * &2)) l" c s u c s v s c;;
let C1092MTFER_R = c1092mtfer_tr 10;;

let C1092MTFER_TR_INSIDE = prove
 (`forall c s u v a x y. linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a x y <=>
                   linside c s u v a (&2 + x) (&2 + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* the closed center sign of the right wall owner (WallContext, wall 2, branch false) *)
let C1092MTFER_CUT = prove
 (parse_term (Printf.sprintf "!%s. %s ==> &2 <= lcy %s %s %s %s l" C1092AE_P C1092MMPE_CTX
    (c1092mtfer_q 10 "ooc") (c1092mtfer_q 10 "oos") (c1092mtfer_q 10 "oou") (c1092mtfer_q 10 "oov")),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092wc_ctx] THEN DISCH_THEN(MP_TAC o SPEC `2`) THEN
  REWRITE_TAC[ARITH; c1092mmpe_mmmp; c1092wc_wfc; c1092wc_wfs; c1092wc_wfu; c1092wc_wfv;
              c1092wc_lfc; c1092wc_lfs; c1092wc_lfu; c1092wc_lfv] THEN
  REWRITE_TAC(Array.to_list C1092WC_WALL_ELS) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[lcy] THEN REAL_ARITH_TAC);;

(* Lean: right_profile *)
let C1092MTFER_RIGHT_PROFILE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> C1092TF_right %s" C1092AE_P C1092AE_HYP
    C1092MMPE_CTX (c1092mmpe_in 10 "&3" "&87 / &50") C1092MTFER_R),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MTFER_CUT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MRF_POINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`EL 10 c1092wc_code`]) OO_BOX) THEN
  MP_TAC(SPECL (C1092MMPE_V @ [`EL 10 c1092wc_code`]) OO_UNIT) THEN
  ASM_REWRITE_TAC[lcont] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[C1092TF_right; C1092MTFER_TR_INSIDE] THEN REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`&87 / &50`; `&12 / &5`] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    RASM_ARITH_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
    DISCH_THEN(MP_TAC o SPECL [`&2 + x`; `&2 + y`]) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN REWRITE_TAC[lcy] THEN RASM_ARITH_TAC]);;

(* Lean: input_of_profiles *)
let C1092MTFER_INPUT_OF_PROFILES = prove
 (parse_term (Printf.sprintf "!%s cE sE uE vE aE cN sN uN vN aN.
     %s /\\ %s /\\ %s /\\ cE * cE + sE * sE = &1 /\\ &0 < aE /\\ aE = l /\\
     (!x y. linside cE sE uE vE aE x y <=> %s) /\\
     c1092mnas_pos %s cN sN uN vN aN /\\ C1092TF_southeast cE sE uE vE aE /\\ &3 * sN <= &1 + cN
     ==> C1092TF_input cE sE uE vE aE cN sN uN vN aN %s"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX (c1092mmpe_in 10 "&3" "&87 / &50")
    (c1092mmpe_in 5 "&2 + x" "&2 + y") C1092AE_P C1092MTFER_R),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MTFEN_NORTHEAST_CORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MTFER_RIGHT_PROFILE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC (parse_term (Printf.sprintf "c1092mnas_pos %s cN sN uN vN aN" C1092AE_P)) THEN
  REWRITE_TAC[c1092mnas_pos] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aN:real = l`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = l`)) THEN
  REWRITE_TAC[C1092TF_input] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC C1092MTFEN_NORTHEASTCORE_COMPLETE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[ldisj; C1092MTFER_TR_INSIDE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC C1092MO_CODE_CONV THEN REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (c1092mo_apart 5 10);
    REWRITE_TAC[ldisj; C1092MTFER_TR_INSIDE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC C1092MO_CODE_CONV THEN REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC (c1092mo_apart 6 10)]);;

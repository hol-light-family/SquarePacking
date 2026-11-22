(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/BottomOriginEntrance.lean           *)
(* (N12Compact.C1092MMMPBottomOriginEntrance).  Literal actual-owner entrance*)
(* from DOUBLE-RIGHT-BOTTOM-ORIGIN section 4 / RIGHT-NEAR-BOTTOM-ORIGIN      *)
(* section 3.  Conventions of CP_C1092_MMMP_SoutheastSign.ml (forward toolkit*)
(* c1092mo_* of CP_C1092_MMMP_Origins.ml; c1092mo_origin is boundary_origin  *)
(* OCWPBO_BOUNDARY_ORIGIN for pulled owners; PositiveActual is                *)
(* c1092mss_positiveActual).  C1092MMMPPositiveInwardHalfangle.point is      *)
(* C1092MPIH_POINT; C1092WallProfileScalars.half is C1092WPS_half.           *)
(* Tag C1092MBOE_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_PositiveInwardHalfangle.ml";;
needs "n12/geometry/CP_C1092_MMMP_SoutheastSign.ml";;

let C1092MBOE_MISSING = "~" ^ c1092mmpe_in 9 "&2" "&1";;
let C1092MBOE_HALF = c1092mmpe_in 1 "&3" "&3 / &2";;

(* Lean: corner_halfpoint *)
let C1092MBOE_CORNER_HALFPOINT = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    C1092MBOE_MISSING C1092MBOE_HALF),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092MO_CODE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  let bottom = c1092mo_use C1092MBP_PAIR in
  let absent = mk_neg (c1092mo_in 1 `&3` `&3 / &2`) in
  let th = c1092mo_origin [C1092MO_X] 9 1 `&457 / &500` `&8 / &5`
    [c1092mo_seed 9 (`&2`, `&457 / &500`); CONJUNCT1 bottom;
     c1092mo_seed 1 (`&3`, `&457 / &500`); c1092mo_seed 1 (`&3`, `&1`); ASSUME absent]
    [`&4 - x`; `y:real`] in
  UNDISCH_TAC (mk_neg (c1092mo_in 9 `&2` `&1`)) THEN REWRITE_TAC[th]);;

(* Lean: southeast_halfangle *)
let C1092MBOE_SOUTHEAST_HALFANGLE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ ~%s /\\ %s
      ==> ?cC sC uC vC aC. cC * cC + sC * sC = &1 /\\ &0 < aC /\\
            c1092mss_positiveActual c1 c2 a b l cC sC uC vC aC /\\
            linside cC sC uC vC aC (&1) (C1092WPS_half cC sC)"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX C1092MSS_NEAR (c1092mmpe_in 5 "&3" "&8 / &5") C1092MBOE_MISSING),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MSS_INWARD_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MBOE_CORNER_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MSS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mss_positiveActual] o
    check (fun th -> can (term_match [] `c1092mss_positiveActual c1 c2 a b l cC sC uC vC aC`) (concl th))) THEN
  MATCH_MP_TAC C1092MPIH_POINT THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  let bottom = c1092mo_use C1092MBP_PAIR in
  let lit s = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term s)) in
  ASM_REWRITE_TAC[c1092mo_seed 5 (`&47 / &20`, `&33 / &20`);
    c1092mo_excl 5 7 (c1092mo_use C1092MPC_NORTHWEST_CENTER);
    c1092mo_excl 5 1 (lit C1092MBOE_HALF); c1092mo_excl 5 9 (CONJUNCT2 bottom)] THEN
  MP_TAC(SPECL C1092MMPE_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

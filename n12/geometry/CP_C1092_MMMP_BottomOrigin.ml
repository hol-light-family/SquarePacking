(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/BottomOrigin.lean                   *)
(* (N12Compact.C1092MMMPBottomOrigin).  Actual-owner conclusions of          *)
(* DOUBLE-RIGHT-BOTTOM-ORIGIN sections 4--5.  Conventions of                 *)
(* CP_C1092_MMMP_BottomOriginEntrance.ml / CP_C1092_MMMP_SoutheastSign.ml    *)
(* (PositiveActual is c1092mss_positiveActual; forward toolkit c1092mo_).    *)
(* W = (pullSwap (pullY (owners p 9))).translated 2 2 is the tuple           *)
(* c1092mss_chart (owners p 9) (C1092MSS_INSIDE_CHART: inside x y <=>        *)
(* owners p 9 inside (2 + y) (2 - x)).  BottomOriginObstruction.impossible   *)
(* C1092BOO_IMPOSSIBLE; PositiveInwardHalfangle.small_angle_of_bar           *)
(* C1092MPIH_SMALL_ANGLE_OF_BAR; inside_segment C1092WC_INSIDE_SEGMENT.      *)
(* Tag C1092MBO_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_BottomOriginEntrance.ml";;
needs "n12/geometry/CP_C1092_MMMP_BottomOriginObstruction.ml";;

let C1092MBO_OUTER = "~" ^ c1092mmpe_in 5 "&3" "&8 / &5";;
let C1092MBO_ORIGIN = c1092mmpe_in 9 "&2" "&1";;

(* the facts of the PositiveActual square E = cE sE uE vE l after the substitution aE = l *)
let C1092MBO_E_TAC =
  MP_TAC(SPEC_ALL C1092MSS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[c1092mss_positiveActual] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = l`));;

(* Lean: point_of_near *)
let C1092MBO_POINT_OF_NEAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    C1092MSS_NEAR C1092MBO_OUTER C1092MBO_ORIGIN),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MSS_INWARD_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MBOE_CORNER_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MBO_E_TAC THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let o9 = c1092mo_own 9 in
  let tW = c1092mss_chart o9 in
  let bottom = c1092mo_use C1092MBP_PAIR in
  let corner = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term C1092MBOE_HALF)) in
  let box9 = REWRITE_RULE[lcont] (c1092mo_box 9) in
  MATCH_MP_TAC (SPECL ([`cE:real`; `sE:real`; `uE:real`; `vE:real`; `l:real`] @ tW) C1092BOO_IMPOSSIBLE) THEN
  REWRITE_TAC[ldisj; C1092MSS_INSIDE_CHART] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ASM_REWRITE_TAC[CONJUNCT1 bottom; CONJUNCT2 bottom; c1092mo_seed 5 (`&47 / &20`, `&33 / &20`);
    c1092mo_seed 9 (`&2`, `&457 / &500`);
    c1092mo_excl 5 7 (c1092mo_use C1092MPC_NORTHWEST_CENTER); c1092mo_excl 5 1 corner;
    REWRITE_RULE[ldisj] (c1092mo_apart 5 9); MATCH_MP C1092MSS_CHART_UNIT (c1092mo_unit 9);
    c1092mo_side (); c1092mo_pos ()] THEN
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box9) THEN REAL_ARITH_TAC);;

(* the strict bottom bar (local fact) *)
let C1092MBO_BAR = prove
 (`forall c s u v a y. linside c s u v a (&2) (&1) /\ linside c s u v a (&12 / &5) (&1) /\
     &0 <= y /\ y <= &2 / &5 ==> linside c s u v a (&2 + y) (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&2`; `&1`; `&12 / &5`; `&1`;
                `&5 / &2 * y`] C1092WC_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN REAL_ARITH_TAC);;

(* Lean: small_angle_of_near *)
let C1092MBO_SMALL_ANGLE_OF_NEAR = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s /\\ %s
      ==> ?cC sC uC vC aC. cC * cC + sC * sC = &1 /\\ &0 < aC /\\
            c1092mss_positiveActual c1 c2 a b l cC sC uC vC aC /\\
            sC + (&2 / &5) * cC < &3 / &5 /\\ sC < &21 / &100 /\\ &97 / &100 < cC"
    C1092AE_P C1092AE_HYP C1092MMPE_CTX C1092MSS_NEAR C1092MBO_OUTER),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MBO_POINT_OF_NEAR) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MSS_INWARD_PAIR) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MSS_EXISTS_POSITIVE) THEN ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mss_positiveActual] o
    check (fun th -> can (term_match [] `c1092mss_positiveActual c1 c2 a b l cC sC uC vC aC`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`] C1092MPIH_SMALL_ANGLE_OF_BAR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    (let bottom = c1092mo_use C1092MBP_PAIR in
    let origin = CONV_RULE C1092MO_CODE_CONV (ASSUME (parse_term C1092MBO_ORIGIN)) in
    let bar = GEN `y:real` (DISCH `&0 <= y /\ y <= &2 / &5`
      (c1092mo_excl 5 9 (MATCH_MP C1092MBO_BAR (end_itlist CONJ
         [origin; CONJUNCT1 bottom; CONJUNCT1 (ASSUME `&0 <= y /\ y <= &2 / &5`);
          CONJUNCT2 (ASSUME `&0 <= y /\ y <= &2 / &5`)])))) in
    ASM_REWRITE_TAC[c1092mo_seed 5 (`&47 / &20`, `&33 / &20`);
      c1092mo_excl 5 7 (c1092mo_use C1092MPC_NORTHWEST_CENTER); REAL_ARITH `&2 - &1 = &1`] THEN
    REPEAT CONJ_TAC THEN
    FIRST [ACCEPT_TAC bar; MP_TAC(c1092mo_side ()) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);
    SIMP_TAC[]]);;

(* Lean: point_of_lower *)
let C1092MBO_POINT_OF_LOWER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP C1092MMPE_CTX
    (c1092mmpe_in 10 "&3" "&8 / &5") C1092MBO_ORIGIN),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MMPE_WALL_AUXILIARIES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term C1092MSS_NEAR) ASSUME_TAC THENL
   [MP_TAC(SPECL (fst (chop_list 5 (snd (strip_comb (parse_term C1092MSS_NEAR)))) @
                  [`&3`; `&8 / &5`; `&3`; `&113 / &50`; `&7 / &33`]) C1092WC_INSIDE_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC C1092MBO_POINT_OF_NEAR THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  ACCEPT_TAC(c1092mo_excl 5 10 (CONV_RULE C1092MO_CODE_CONV
    (ASSUME (parse_term (c1092mmpe_in 10 "&3" "&8 / &5"))))));;

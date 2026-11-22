(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeOwnedPositiveActual.lean     *)
(* (N12Compact.C1092MPPMNegativeOwnedPositiveActual; Lean header: "Source    *)
(* only").  The genuine negative-retaining to positive-retaining angle       *)
(* entrance.  Conventions of CP_C1092_MPPMActualRetaining.ml (owners p i at  *)
(* mask EL i c1092wc_code; ActualFrame c1092psa_frame; (rotation i)          *)
(* .pullPacking p = (d1,d2,e1,e2) with c1092ot_pk (EL i c1092mpapo_rotation);*)
(* SuccessorFrame c1092mar_successorFrame; MMMPEndingAxes.clockwise D =      *)
(* (cD, sD, --vD - aD, uD, aD), its triple turn W = (cD, sD, vD, --uD - aD,  *)
(* aD) (C1092MABO_INSIDE_CLOCKWISE3)).  (owners p' 9).translated 2 2 of a    *)
(* packing p' is c1092nopa_tr (C1092PSA_INSIDE_TRANSLATED).  Inputs:         *)
(* NegativeOwnedPositiveCeiling c1092nopcl_input / C1092NOPCL_HALF_LT;       *)
(* MPPMNegativeForward c1092nff_input; NegativeOwnedPositiveExclusion        *)
(* c1092nopx_input / C1092NOPX_IMPOSSIBLE; AllNonpositive.clearance          *)
(* C1092ANC_CLEARANCE; ActualNonpositive.actual_core / bottom_bar C1092MANC_*;*)
(* positive_faces C1092MABO_POSITIVE_FACES.  The private marker_point is     *)
(* oo_seed (c1092psa_seed).  Tag C1092NOPA_.                                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveCeiling.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveExclusion.ml";;
needs "n12/geometry/CP_C1092_MPPMActualRetaining.ml";;

(* Lean: marker_point (private) *)
let C1092NOPA_MARKER_POINT = C1092PSA_MARKER_POINT;;

(* (owners pk i).translated 2 2, EL-coded masks *)
let c1092nopa_tr pk i =
  let m = mk_comb(mk_comb(`EL:num->(num)list->num`, mk_small_numeral i), `c1092wc_code`) in
  let [c; s; u; v] = map (fun f -> list_mk_comb(f, pk @ [m])) [`ooc`; `oos`; `oou`; `oov`] in
  [c; s; mk_binop `(-):real->real->real` u (parse_term (Printf.sprintf "%s * &2 + %s * &2"
      (string_of_term c) (string_of_term s)));
   mk_binop `(-):real->real->real` v (parse_term (Printf.sprintf "--%s * &2 + %s * &2"
      (string_of_term s) (string_of_term c)));
   `l:real`];;
let c1092nopa_trs pk i = String.concat " " (map (fun t -> "(" ^ string_of_term t ^ ")") (c1092nopa_tr pk i));;

(* ~ owner i at (x,y) of the packing pk, from owner j at (x,y) in the assumptions *)
let c1092nopa_excl_tac pk i j x y =
  MP_TAC(SPECL (pk @ [mk_small_numeral i; mk_small_numeral j]) C1092WC_OWNERS_DISJOINT) THEN
  ASM_REWRITE_TAC[ldisj; ARITH] THEN DISCH_THEN(MP_TAC o SPECL [x; y]) THEN ASM_REWRITE_TAC[];;

let C1092NOPA_CFR c4 = list_mk_comb(`c1092psa_frame`, c4);;
let c1092nopa_frame_of v th =
  c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = v;;

let C1092NOPA_DPK3 = C1092MAR_DPK3;;

(* Lean: positive_half_angle *)
let C1092NOPA_POSITIVE_HALF_ANGLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s /\\ %s /\\
      %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD (--sD) /\\ %s
      ==> sC / (&1 + cC) < &11 / &100"
    C1092AE_P C1092MABO_PHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092NOPA_DPK3 C1092MAR_DSQ
    (c1092mppe_in 7 "&2" "&113 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_POSITIVE_FACES) THEN
  ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  C1092MPAPO_ORD_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092NOPA_DPK3)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,false,true)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 3 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 3 THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2")) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (parse_term (c1092ae_in "d1 d2 e1 e2 l" 5 "&2" "&87 / &50")) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [5] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* nextMissing *)
  SUBGOAL_THEN `~linside cD sD uD vD aD (&0) (--(&13 / &50))` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if c1092nopa_frame_of `d1:num->real` th
      then REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092psa_frame] th)] else NO_TAC) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    c1092nopa_excl_tac C1092MANH_D5 4 5 `&2` `&87 / &50`;
    ALL_TAC] THEN
  (* bar *)
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x. --(&14 / &25) <= x ==> x <= &0 ==> linside %s x (--(&1))"
      (c1092nopa_trs C1092MANH_D5 9))) ASSUME_TAC THENL
   [REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MANC_BOTTOM_BAR) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MAR_DV @ c1092nopa_tr C1092MANH_D5 9) C1092ANC_CLEARANCE) THEN
  ANTS_TAC THENL
   [MP_TAC(SPECL (C1092MANH_D5 @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
    MP_TAC(SPECL C1092MANH_D5 OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY RASM_ARITH_TAC THEN
    REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
    FIRST_ASSUM(fun th -> if c1092nopa_frame_of `d1:num->real` th
      then REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092psa_frame] th)] else NO_TAC) THEN
    MP_TAC(SPECL (C1092MANH_D5 @ [`4`; `9`]) C1092WC_OWNERS_DISJOINT) THEN
    ASM_REWRITE_TAC[ldisj; ARITH] THEN MESON_TAC[];
    DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_cleared; c1092anc_faces] o
    check (c1092mpapo_head `c1092anc_cleared`)) THEN
  (* the triple turn W of D is the original owner 7 *)
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x y. linside cD sD vD (--uD - aD) aD x y <=> %s"
      (c1092mppe_in 7 "&2 + x" "&2 + y"))) ASSUME_TAC THENL
   [REWRITE_TAC[C1092MABO_INSIDE_CLOCKWISE3] THEN
    FIRST_ASSUM(fun th -> if c1092nopa_frame_of `d1:num->real` th
      then REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092psa_frame] th)] else NO_TAC) THEN
    c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [4] THEN C1092MAR_POINT_EQ_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ [`cD:real`; `sD:real`; `vD:real`; `--uD - aD`; `aD:real`])
    C1092NOPCL_HALF_LT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  REWRITE_TAC[c1092nopcl_input; ldisj] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 7 (`&33 / &20`, `&47 / &20`);
              c1092psa_apart 4 7] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC);;

let C1092NOPA_D2PK3 = string_of_term (c1092mar_pk `EL 3 c1092mpapo_rotation` C1092MAR_D C1092MAR_D2);;

(* Lean: recipient_half_angle *)
let C1092NOPA_RECIPIENT_HALF_ANGLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s /\\ %s /\\ c977cc_normal cC (--sC) /\\
      %s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD sD /\\ &0 < sD /\\ %s
      ==> sD / (&1 + cD) < &11 / &100"
    C1092AE_P C1092MPAPO_HYPS C1092MPOA_CHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MAR_DPK1 C1092MAR_DSQ
    (c1092mppe_in 5 "&2" "&87 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `d10:num->real` (X_CHOOSE_THEN `d20:num->real` (X_CHOOSE_THEN `e10:num->real`
    (X_CHOOSE_THEN `e20:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d10:num->real`, list_mk_exists([`d20:num->real`; `e10:num->real`; `e20:num->real`],
       c1092mar_pk `EL 0 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D0)))) THEN
  X_CHOOSE_THEN `d12:num->real` (X_CHOOSE_THEN `d22:num->real` (X_CHOOSE_THEN `e12:num->real`
    (X_CHOOSE_THEN `e22:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d12:num->real`, list_mk_exists([`d22:num->real`; `e12:num->real`; `e22:num->real`],
       c1092mar_pk `EL 3 c1092mpapo_rotation` C1092MAR_D C1092MAR_D2)))) THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D0 @ C1092MAR_CV) C1092MAR_IDENTITY_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ [`1`; `3`] @ C1092MAR_D0 @ C1092MAR_D @ C1092MAR_D2 @ C1092MAR_CV)
    C1092MAR_ROTATED_FRAME) THEN
  REWRITE_TAC[c1092mar_addSector] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK1)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,true,false)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 1 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 1 THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MANH_D5 @ C1092MAR_DV @ C1092MAR_D2 @ C1092MAR_CV) C1092NOPA_POSITIVE_HALF_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [4; 7] THEN ASM_REWRITE_TAC[]);;

let C1092NOPA_B = c1092nopa_trs C1092MAR_V 9;;
let C1092NOPA_FHYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\
      c977cc_normal cD sD /\\ %s"
  C1092NFA_NHYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MAR_DPK1 C1092MAR_DSQ (c1092mppe_in 5 "&2" "&87 / &50");;

(* Lean: forward_input *)
let C1092NOPA_FORWARD_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s
      ==> c1092nff_input cC sC uC vC aC cD sD (--vD - aD) uD aD %s"
    C1092AE_P C1092NOPA_FHYPS C1092NOPA_B),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x. --(&14 / &25) <= x ==> x <= &0 ==> %s"
      (c1092mppe_in 9 "&2 + x" "&1"))) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV) C1092MANC_BOTTOM_BAR) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o check (c1092mpapo_head `c1092anc_core`)) THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[c1092mar_successorFrame] o
    check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  C1092MPAPO_ORD_TAC THEN
  REWRITE_TAC[c1092nff_input; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
              c1092psa_apart 4 5; c1092psa_apart 4 9] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC);;

(* Lean: retaining_edge_impossible *)
let C1092NOPA_RETAINING_EDGE_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD. %s /\\ &0 < sD ==> F"
    C1092AE_P C1092NOPA_FHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092NOPA_RECIPIENT_HALF_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092NOPA_FORWARD_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ C1092MAR_E @ c1092nopa_tr C1092MAR_V 9) C1092NOPX_IMPOSSIBLE) THEN
  MP_TAC(SPECL (C1092MAR_V @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[c1092nopx_input] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `sD / (&1 + cD) <= &7 / &32` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[c1092mar_successorFrame] o
    check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aD:real = l`)) THEN
  REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_excl 5 1 (c1092psa_seed 1 (`&3`, `&1`)); c1092psa_apart 5 9] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
  REWRITE_TAC[c1092psa_apart 5 10] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`&3`; `&36 / &25`] (c1092psa_apart 5 10)) THEN ASM_REWRITE_TAC[]);;

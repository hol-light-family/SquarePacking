(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualRetaining.lean                 *)
(* (N12Compact.C1092MPPMActualRetaining; Lean header: "Source only,          *)
(* uncompiled").  Actual ordinary positive crosspoint seeds and the positive *)
(* retaining successor corollary.  Conventions of                            *)
(* CP_C1092_MPPMActualBoundaryOrigin.ml: owners p i at mask EL i             *)
(* c1092wc_code, side l; Ordinary p is c1092mpapo_ordinary; ActualFrame p C  *)
(* is c1092psa_frame; (rotation i).pullPacking p is the packing (d1,..) with *)
(* c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2) (the    *)
(* rotations are (F,F,F), (T,T,F), (F,T,T), (T,F,T)); a pulled packing of a  *)
(* pulled packing uses the variables d1k d2k e1k e2k.  SuccessorFrame is     *)
(* c1092mar_successorFrame; addSector is c1092mar_addSector (num, i, j < 4); *)
(* MMMPEndingAxes.clockwise (c,s,u,v,a) is (c, s, --v - a, u, a)             *)
(* (C1092MEA_INSIDE_CLOCKWISE).  Shallow / Steep / classify:                 *)
(* c1092pad_shallow / c1092pad_steep / C1092PAD_CLASSIFY; PositiveRetaining- *)
(* Steep Input / impossible: c1092prst_input (with c1092prfnt_input) /       *)
(* C1092PRST_IMPOSSIBLE.  Tag C1092MAR_.                                     *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualBoundaryOrigin.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveCrosspointAngleDichotomy.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteep.ml";;

(* Lean: side_gt (private) *)
let C1092MAR_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092MAR_SIDE_SAME = C1092MPAPO_SIDE_SAME;;
(* Lean: mark (private) *)
let C1092MAR_MARK = C1092MPAPO_MARK;;

let C1092MAR_V = C1092MPPE_V;;
let C1092MAR_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MAR_DV = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`];;
let c1092mar_pk g base4 d4 =
  mk_eq(list_mk_comb(`c1092ot_pk`, [g; end_itlist (curry mk_pair) base4]), end_itlist (curry mk_pair) d4);;

(* rewrite the owners idx of the packing d4 (pulled from base4 by g) to the owners of base4 *)
let c1092mar_pull_tac base4 d4 g idx =
  MAP_EVERY (fun i ->
    MP_TAC(SPECL ([g] @ base4 @ [`l:real`] @ d4 @ [mk_small_numeral i]) C1092OT_OWNERS_TRANSPORT) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE ARITH_TAC); ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP C1092CT_INSIDE_PULL th])) idx THEN
  REWRITE_TAC(map (fun i -> c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral i))) idx) THEN
  REWRITE_TAC[c1092ct_apx; c1092ct_apy; LET_DEF; LET_END_DEF] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];;
let c1092mar_act g i =
  dest_small_numeral (rhs (concl (c1092ae_act_conv (mk_comb(mk_comb(`c1092ws_owner_action`, g), mk_small_numeral i)))));;

(* NPACK / IMAGE of a pulled packing d4 = pk g base4 *)
let c1092mar_pk_facts_tac g base4 d4 =
  SUBGOAL_THEN (list_mk_comb(`NPACK`, d4 @ [`l:real`])) ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: base4) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`IMAGE binarysum`, list_mk_comb(`FFP`, d4 @ [`l:real`])), `c1092wc_family`))
    ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: base4) THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC];;

(* the coordinates of two owner points agree: finish an equivalence of insides *)
let C1092MAR_SAME_POINT = prove
 (`forall P:real->real->bool x1 y1 x2 y2. x1 = x2 /\ y1 = y2 ==> (P x1 y1 <=> P x2 y2)`,
  MESON_TAC[]);;
let C1092MAR_POINT_EQ_TAC =
  REPEAT GEN_TAC THEN MATCH_MP_TAC C1092MAR_SAME_POINT THEN CONJ_TAC THEN REAL_ARITH_TAC;;

(* Lean: SuccessorFrame (structure) *)
let c1092mar_successorFrame = new_definition (parse_term (Printf.sprintf
  "c1092mar_successorFrame (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                           (cE:real) (sE:real) (uE:real) (vE:real) (aE:real) <=>
     aE = l /\\ !x y. linside cE sE uE vE aE x y <=> %s"
  (c1092mppe_in 5 "&2 + x" "&2 + y")));;

(* Lean: addSector *)
let c1092mar_addSector = new_definition `c1092mar_addSector (i:num) (j:num) = (i + j) MOD 4`;;

let C1092MAR_D0 = c1092mpapo_d4 "0";;
let C1092MAR_D = c1092mpapo_d4 "";;

(* Lean: identity_frame *)
let C1092MAR_IDENTITY_FRAME = prove
 (parse_term (Printf.sprintf "!%s d10 d20 e10 e20 cC sC uC vC aC. %s /\\ %s /\\ c1092psa_frame c1 c2 a b l cC sC uC vC aC
      ==> c1092psa_frame d10 d20 e10 e20 l cC sC uC vC aC"
    C1092AE_P C1092AE_HYP (string_of_term (c1092mar_pk `EL 0 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D0))),
  REPEAT GEN_TAC THEN REWRITE_TAC C1092MPAPO_ROT_ELS THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092psa_frame c1 c2 a b l cC sC uC vC aC` THEN
  REWRITE_TAC[c1092psa_frame] THEN c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D0 `(false,false,false)` [4]);;

(* Lean: original_frame *)
let C1092MAR_ORIGINAL_FRAME = prove
 (parse_term (Printf.sprintf "!%s d10 d20 e10 e20 cC sC uC vC aC. %s /\\ %s /\\ c1092psa_frame d10 d20 e10 e20 l cC sC uC vC aC
      ==> c1092psa_frame c1 c2 a b l cC sC uC vC aC"
    C1092AE_P C1092AE_HYP (string_of_term (c1092mar_pk `EL 0 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D0))),
  REPEAT GEN_TAC THEN REWRITE_TAC C1092MPAPO_ROT_ELS THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092psa_frame d10 d20 e10 e20 l cC sC uC vC aC` THEN
  REWRITE_TAC[c1092psa_frame] THEN c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D0 `(false,false,false)` [4]);;

let C1092MAR_D1 = c1092mpapo_d4 "1";;
let C1092MAR_D2 = c1092mpapo_d4 "2";;

(* Lean: rotated_frame *)
let C1092MAR_ROTATED_FRAME =
  let case i j =
    let gi = el i C1092MPAPO_ROTS and gj = el j C1092MPAPO_ROTS
    and gij = el ((i + j) mod 4) C1092MPAPO_ROTS in
    REWRITE_TAC(c1092mar_addSector :: C1092MPAPO_ROT_ELS) THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC C1092MPAPO_ROT_ELS THEN STRIP_TAC THEN
    c1092mar_pk_facts_tac gi C1092MPAPO_V4 C1092MAR_D1 THEN
    UNDISCH_TAC (list_mk_comb(`c1092psa_frame`, C1092MAR_D0 @ [`l:real`] @ C1092MAR_CV)) THEN
    REWRITE_TAC[c1092psa_frame] THEN
    c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D0 gij [4] THEN
    c1092mar_pull_tac C1092MAR_D1 C1092MAR_D2 gj [4] THEN
    c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D1 gi [c1092mar_act gj 4] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN C1092MAR_POINT_EQ_TAC in
  prove
   (parse_term (Printf.sprintf "!%s i j d10 d20 e10 e20 d11 d21 e11 e21 d12 d22 e12 e22 cC sC uC vC aC.
        %s /\\ i < 4 /\\ j < 4 /\\ %s /\\ %s /\\ %s /\\ c1092psa_frame d10 d20 e10 e20 l cC sC uC vC aC
        ==> c1092psa_frame d12 d22 e12 e22 l cC sC uC vC aC"
      C1092AE_P C1092AE_HYP
      (string_of_term (c1092mar_pk `EL (c1092mar_addSector i j) c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D0))
      (string_of_term (c1092mar_pk `EL i c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D1))
      (string_of_term (c1092mar_pk `EL j c1092mpapo_rotation` C1092MAR_D1 C1092MAR_D2))),
    REPEAT GEN_TAC THEN
    ASM_CASES_TAC `i < 4` THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `j < 4` THEN ASM_REWRITE_TAC[] THEN
    C1092WP_ENUM_TAC `i:num` 4 THEN C1092WP_ENUM_TAC `j:num` 4 THEN
    REWRITE_TAC[ARITH] THENL
     (List.concat (map (fun i -> map (fun j -> case i j) [0; 1; 2; 3]) [0; 1; 2; 3])));;

let C1092MAR_DPK1 = string_of_term (c1092mar_pk `EL 1 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D);;
let C1092MAR_E = [`cD:real`; `sD:real`; `--vD - aD`; `uD:real`; `aD:real`];;

(* Lean: successor_frame *)
let C1092MAR_SUCCESSOR_FRAME = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2 cD sD uD vD aD. %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD
      ==> c1092mar_successorFrame %s cD sD (--vD - aD) uD aD"
    C1092AE_P C1092AE_HYP C1092MAR_DPK1 C1092AE_P),
  REPEAT GEN_TAC THEN REWRITE_TAC C1092MPAPO_ROT_ELS THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD` THEN
  REWRITE_TAC[c1092psa_frame; c1092mar_successorFrame; C1092MEA_INSIDE_CLOCKWISE] THEN
  c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [4] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN C1092MAR_POINT_EQ_TAC);;

let C1092MAR_CHYPS = Printf.sprintf "%s /\\ c977cc_normal cC sC /\\ &0 < sC" C1092MPOA_CHYPS;;

(* Lean: forward_crosspoint *)
let C1092MAR_FORWARD_CROSSPOINT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ %s ==> %s"
    C1092AE_P C1092MPAPO_HYPS (c1092mppe_in 4 "&87 / &50" "&2") C1092MAR_CHYPS (c1092mppe_in 4 "&3 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_POSITIVE_PREVIOUS_EXCLUDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV) C1092PSA_FORWARD_CROSSPOINT) THEN ASM_REWRITE_TAC[]);;

let C1092MAR_DSQ = "cD * cD + sD * sD = &1 /\\ &0 < aD";;

(* Lean: retaining_successor_shallow *)
let C1092MAR_RETAINING_SUCCESSOR_SHALLOW = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD.
      %s /\\ %s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD sD /\\ &0 < sD /\\
      %s /\\ %s ==> c1092pad_shallow cD sD uD vD aD"
    C1092AE_P C1092MPAPO_HYPS C1092MAR_CHYPS C1092MAR_DPK1 C1092MAR_DSQ
    (c1092mppe_in 5 "&2" "&87 / &50") (c1092mppe_in 6 "&5 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`])
    C1092MAR_SUCCESSOR_FRAME) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK1)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,true,false)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 1 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 1 THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (c1092ae_in "d1 d2 e1 e2 l" 4 "&87 / &50" "&2")) ASSUME_TAC THENL
   [c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,true,false)` [4] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MABO_POSITIVE_PREVIOUS_EXCLUDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANH_D5 C1092MPAWR_BOTTOM_ORDINARY) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANH_D5 C1092MPAPO_FAR_POINTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mpapo_ordinary] o
    check (fun th -> c1092mpapo_head `c1092mpapo_ordinary` th &&
                     hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092PSA_FORWARD_CORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092PSA_FORWARD_INPUTS) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&1 < aD` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o
      check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT2 o REWRITE_RULE[c1092mar_successorFrame] o check (c1092mpapo_head `c1092mar_successorFrame`)) THEN
  (* nextMissing *)
  SUBGOAL_THEN `~linside cD sD uD vD aD (&0) (--(&1 / &2))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM C1092MEA_INSIDE_CLOCKWISE] THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN c1092mano_excl_tac 5 6 `&5 / &2` `&2`;
    ALL_TAC] THEN
  MP_TAC(SPECL C1092MAR_DV C1092PAD_CLASSIFY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(ACCEPT_TAC o last o CONJUNCTS o REWRITE_RULE[c1092pcs_forwardInputs] o
      check (c1092mpapo_head `c1092pcs_forwardInputs`));
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN
  (* steep: the retaining theorem *)
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MABO_POSITIVE_FACES) THEN ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_DV) C1092MABO_POSITIVE_FACES) THEN ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pad_steep] o check (c1092mpapo_head `c1092pad_steep`)) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`] C1092MABO_STEEP_SINE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pcs_forwardCore] o check (c1092mpapo_head `c1092pcs_forwardCore`)) THEN
  SUBGOAL_THEN `--(&13 / &50) * cD < uD + aD /\ &0 < vD + aD` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cD sD uD vD aD (--(&13 / &50)) (&0)` THEN REWRITE_TAC[linside] THEN
    UNDISCH_TAC `&0 < sD` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o
      check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `c1:num->real`)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY (fun (c, s) -> c1092mabo_normal_tac c s) [`cC:real`, `sC:real`; `cD:real`, `sD:real`] THEN
  MP_TAC(SPECL (C1092MAR_CV @ C1092MAR_E) C1092PRST_IMPOSSIBLE) THEN
  REWRITE_TAC[c1092prst_input; c1092prfnt_input; ldisj] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `c1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th && hd (snd (strip_comb (concl th))) = `d1:num->real`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aD:real = l`))) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
              c1092psa_apart 4 5] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC);;

let C1092MAR_WV = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;
let C1092MAR_DPK3 = string_of_term (c1092mar_pk `EL 3 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D);;
let C1092MAR_RHYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ cW * cW + sW * sW = &1 /\\ &0 < aW /\\
      c1092psa_frame d1 d2 e1 e2 l cW sW uW vW aW /\\ c977cc_normal cW sW /\\ &0 < sW /\\ %s /\\ %s"
  C1092MPAPO_HYPS C1092MAR_CHYPS C1092MAR_DPK3 (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 5 "&2" "&3 / &2");;

(* Lean: retaining_shallow *)
let C1092MAR_RETAINING_SHALLOW = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cW sW uW vW aW. %s ==> c1092pad_shallow cC sC uC vC aC"
    C1092AE_P C1092MAR_RHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_CHOOSE_THEN `d10:num->real` (X_CHOOSE_THEN `d20:num->real` (X_CHOOSE_THEN `e10:num->real`
    (X_CHOOSE_THEN `e20:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d10:num->real`, list_mk_exists([`d20:num->real`; `e10:num->real`; `e20:num->real`],
       c1092mar_pk `EL 0 c1092mpapo_rotation` C1092MPAPO_V4 C1092MAR_D0)))) THEN
  X_CHOOSE_THEN `d12:num->real` (X_CHOOSE_THEN `d22:num->real` (X_CHOOSE_THEN `e12:num->real`
    (X_CHOOSE_THEN `e22:num->real` ASSUME_TAC)))
    (MESON[PAIR] (mk_exists(`d12:num->real`, list_mk_exists([`d22:num->real`; `e12:num->real`; `e22:num->real`],
       c1092mar_pk `EL 1 c1092mpapo_rotation` C1092MAR_D C1092MAR_D2)))) THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D0 @ C1092MAR_CV) C1092MAR_IDENTITY_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ [`3`; `1`] @ C1092MAR_D0 @ C1092MAR_D @ C1092MAR_D2 @ C1092MAR_CV)
    C1092MAR_ROTATED_FRAME) THEN
  REWRITE_TAC[c1092mar_addSector] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = parse_term C1092MAR_DPK3)) THEN
  REWRITE_TAC C1092MPAPO_ROT_ELS THEN DISCH_TAC THEN
  c1092mar_pk_facts_tac `(true,false,true)` C1092MPAPO_V4 C1092MAR_D THEN
  c1092mpapo_rot_use C1092MPAPO_ROTATION_CONTEXT "" 3 THEN DISCH_TAC THEN
  c1092mpapo_rot_use C1092MPAPO_ORDINARY_ROTATED "" 3 THEN DISCH_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MANH_D5 @ C1092MAR_WV @ C1092MAR_D2 @ C1092MAR_CV) C1092MAR_RETAINING_SUCCESSOR_SHALLOW) THEN
  ASM_REWRITE_TAC[] THEN
  c1092mar_pull_tac C1092MPAPO_V4 C1092MAR_D `(true,false,true)` [5; 6] THEN ASM_REWRITE_TAC[]);;

(* rewrite the frame of C (an ActualFrame of the packing c1 c2 a b l) into the goal *)
let C1092MAR_CFRAME_TAC =
  FIRST_ASSUM(fun th ->
    if c1092mpapo_head `c1092psa_frame` th && mem `cC:real` (frees (concl th)) &&
       hd (snd (strip_comb (concl th))) = `c1:num->real`
    then REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092psa_frame] th)] else NO_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV);;

(* Lean: retaining_halfpoint_origin *)
let C1092MAR_RETAINING_HALFPOINT_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cW sW uW vW aW. %s
      ==> c1092pad_shallow cC sC uC vC aC /\\ %s /\\ %s"
    C1092AE_P C1092MAR_RHYPS (c1092mppe_in 4 "&1" "&3 / &2") (c1092mppe_in 9 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_WV) C1092MAR_RETAINING_SHALLOW) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (c1092mppe_in 4 "&1" "&3 / &2")) ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o last o CONJUNCTS o REWRITE_RULE[c1092pad_shallow] o check (c1092mpapo_head `c1092pad_shallow`)) THEN
    C1092MAR_CFRAME_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPECL C1092MAR_V C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN SIMP_TAC[]);;

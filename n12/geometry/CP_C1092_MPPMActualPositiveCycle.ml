(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualPositiveCycle.lean             *)
(* (N12Compact.C1092MPPMActualPositiveCycle; Lean header: "Source only,      *)
(* uncompiled").  The actual all-positive ordinary cycle with the scalar     *)
(* inequalities as the only named dependency.  Conventions of                *)
(* CP_C1092_MPPMActualRetaining.ml: owners p i at mask EL i c1092wc_code,    *)
(* side l; Ordinary p c1092mpapo_ordinary; ActualFrame p C c1092psa_frame;  *)
(* (rotation i).pullPacking p is (d1,d2,e1,e2) with                          *)
(* c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2), i < 4  *)
(* (other pulled packings use the suffixed variables d1k d2k e1k e2k);       *)
(* addSector c1092mar_addSector.  ScalarProof / PositiveFrames / Crosspoint /*)
(* Forward / AllCrosspoints: c1092mapc_scalarProof / c1092mapc_positiveFrames*)
(* / c1092mapc_crosspoint / c1092mapc_forward / c1092mapc_allCrosspoints     *)
(* (the OpenSquare invariants of the frame squares are added to the          *)
(* existential of PositiveFrames).  ModesNonnegative / impossible_of_modes:  *)
(* c1092sptg_modesNonnegative / C1092SPTG_IMPOSSIBLE_OF_MODES; actual_input  *)
(* C1092SPTSA_ACTUAL_INPUT.  Tag C1092MAPC_.                                 *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareActual.ml";;

let C1092MAPC_P = C1092AE_P;;

(* Lean: ScalarProof (definition) *)
let c1092mapc_scalarProof = new_definition
 `c1092mapc_scalarProof <=>
    forall c s d t. c977cc_normal c s ==> c977cc_normal d t ==> &3 / &5 <= s ==>
              c1092sptg_modesNonnegative c s d t`;;

(* Lean: PositiveFrames (definition) *)
let c1092mapc_positiveFrames = new_definition (parse_term
  "c1092mapc_positiveFrames (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
     !i d1 d2 e1 e2. i < 4 /\\ c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2)
       ==> ?cC sC uC vC aC. cC * cC + sC * sC = &1 /\\ &0 < aC /\\
             c1092psa_frame d1 d2 e1 e2 l cC sC uC vC aC /\\ c977cc_normal cC sC /\\ &0 < sC");;

(* Lean: Crosspoint (definition) *)
let c1092mapc_crosspoint = new_definition (parse_term (Printf.sprintf
  "c1092mapc_crosspoint (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=> %s"
  (c1092mppe_in 4 "&3 / &2" "&2")));;

(* Lean: Forward (definition) *)
let c1092mapc_forward = new_definition (parse_term (Printf.sprintf
  "c1092mapc_forward (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=> %s"
  (c1092mppe_in 4 "&87 / &50" "&2")));;

(* Lean: AllCrosspoints (definition) *)
let c1092mapc_allCrosspoints = new_definition (parse_term
  "c1092mapc_allCrosspoints (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
     !i d1 d2 e1 e2. i < 4 /\\ c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2)
       ==> c1092mapc_crosspoint d1 d2 e1 e2 l");;

let C1092MAPC_D3 = c1092mpapo_d4 "3";;
let C1092MAPC_D5 = C1092MANH_D5;;

(* choose the pulled packing d4 = pk g base4 *)
let c1092mapc_choose_tac g base4 d4 =
  SUBGOAL_THEN (list_mk_exists(d4, c1092mar_pk g base4 d4)) STRIP_ASSUME_TAC THENL
   [MESON_TAC[PAIR]; ALL_TAC];;

(* NPACK / IMAGE / context / Ordinary of d4 = pk (EL k rotation) base4 *)
let c1092mapc_facts_tac base4 d4 k =
  let g = mk_comb(mk_comb(`EL:num->(bool#bool#bool)list->bool#bool#bool`, k), `c1092mpapo_rotation`) in
  let b5 = base4 @ [`l:real`] in
  SUBGOAL_THEN (list_mk_comb(`NPACK`, d4 @ [`l:real`])) ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_NPACK THEN MAP_EVERY EXISTS_TAC (g :: base4) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN (mk_eq(mk_comb(`IMAGE binarysum`, list_mk_comb(`FFP`, d4 @ [`l:real`])), `c1092wc_family`))
    ASSUME_TAC THENL
   [MATCH_MP_TAC C1092OT_FAMILY_TRANSPORT THEN MAP_EVERY EXISTS_TAC (g :: base4) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (b5 @ d4 @ [k]) C1092MPAPO_ROTATION_CONTEXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
  MP_TAC(SPECL (b5 @ d4 @ [k]) C1092MPAPO_ORDINARY_ROTATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC];;

(* the literal-rotation form of an assumption pk (EL k rotation) base4 = d4 *)
let c1092mapc_lit_tac k base4 d4 =
  ASSUME_TAC(REWRITE_RULE C1092MPAPO_ROT_ELS
    (ASSUME (c1092mar_pk (mk_comb(mk_comb(`EL:num->(bool#bool#bool)list->bool#bool#bool`, k),
                                  `c1092mpapo_rotation`)) base4 d4)));;

let c1092mapc_chain vs ttac = itlist (fun v t -> X_CHOOSE_THEN v t) vs ttac;;

(* from positiveFrames (base) at index k, packing d4: choose the frame square cv *)
let c1092mapc_frame_tac base5 k d4 cv =
  FIRST_ASSUM(MP_TAC o SPECL (k :: d4) o REWRITE_RULE[c1092mapc_positiveFrames] o
    check (fun th -> concl th = list_mk_comb(`c1092mapc_positiveFrames`, base5))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092mar_addSector; MOD_LT_EQ; ARITH]; ALL_TAC] THEN
  DISCH_THEN(c1092mapc_chain cv STRIP_ASSUME_TAC);;

let C1092MAPC_V = C1092MAR_V;;
let C1092MAPC_V4 = C1092MPAPO_V4;;
let C1092MAPC_CV = C1092MAR_CV;;
let C1092MAPC_DV = C1092MAR_DV;;
let C1092MAPC_WV = C1092MAR_WV;;
let C1092MAPC_D = C1092MAR_D;;
let C1092MAPC_D0 = C1092MAR_D0;;
let C1092MAPC_D1 = C1092MAR_D1;;
let C1092MAPC_D2 = C1092MAR_D2;;
let c1092mapc_el k = mk_comb(mk_comb(`EL:num->(bool#bool#bool)list->bool#bool#bool`, k), `c1092mpapo_rotation`);;
let c1092mapc_pk k base4 d4 = c1092mar_pk (c1092mapc_el k) base4 d4;;
let c1092mapc_pks k base4 d4 = string_of_term (c1092mapc_pk k base4 d4);;
let C1092MAPC_SUM = `c1092mar_addSector i j`;;

(* Lean: PositiveFrames.rotated *)
let C1092MAPC_POSITIVEFRAMES_ROTATED = prove
 (parse_term (Printf.sprintf "!%s i d1 d2 e1 e2. %s /\\ c1092mapc_positiveFrames %s /\\ i < 4 /\\ %s
      ==> c1092mapc_positiveFrames d1 d2 e1 e2 l"
    C1092MAPC_P C1092AE_HYP C1092MAPC_P (c1092mapc_pks `i:num` C1092MAPC_V4 C1092MAPC_D)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [c1092mapc_positiveFrames] THEN
  MAP_EVERY X_GEN_TAC (`j:num` :: C1092MAPC_D2) THEN STRIP_TAC THEN
  c1092mapc_choose_tac (c1092mapc_el C1092MAPC_SUM) C1092MAPC_V4 C1092MAPC_D0 THEN
  c1092mapc_frame_tac C1092MAPC_V C1092MAPC_SUM C1092MAPC_D0 C1092MAPC_CV THEN
  MAP_EVERY EXISTS_TAC C1092MAPC_CV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPECL (C1092MAPC_V @ [`i:num`; `j:num`] @ C1092MAPC_D0 @ C1092MAPC_D @ C1092MAPC_D2 @ C1092MAPC_CV)
    C1092MAR_ROTATED_FRAME) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: crosspoint_composed *)
let C1092MAPC_CROSSPOINT_COMPOSED =
  let own = map (fun f -> list_mk_comb(f, C1092MAPC_D0 @ [`l:real`; `EL 4 c1092wc_code`])) [`ooc`; `oos`; `oou`; `oov`] in
  let oc = el 0 own and os = el 1 own and ou = el 2 own and ov = el 3 own in
  let sq = [oc; os; mk_binop `(-):real->real->real` ou (mk_binop `(+):real->real->real`
                     (mk_binop `( * ):real->real->real` oc `&2`) (mk_binop `( * ):real->real->real` os `&2`));
            mk_binop `(-):real->real->real` ov (mk_binop `(+):real->real->real`
                     (mk_binop `( * ):real->real->real` (mk_comb(`(--):real->real`, os)) `&2`)
                     (mk_binop `( * ):real->real->real` oc `&2`)); `l:real`] in
  prove
   (parse_term (Printf.sprintf "!%s i j d10 d20 e10 e20 d1 d2 e1 e2 d12 d22 e12 e22.
        %s /\\ i < 4 /\\ j < 4 /\\ %s /\\ %s /\\ %s /\\ c1092mapc_crosspoint d10 d20 e10 e20 l
        ==> c1092mapc_crosspoint d12 d22 e12 e22 l"
      C1092MAPC_P C1092AE_HYP (c1092mapc_pks C1092MAPC_SUM C1092MAPC_V4 C1092MAPC_D0)
      (c1092mapc_pks `i:num` C1092MAPC_V4 C1092MAPC_D) (c1092mapc_pks `j:num` C1092MAPC_D C1092MAPC_D2)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL (C1092MAPC_V @ [`i:num`; `j:num`] @ C1092MAPC_D0 @ C1092MAPC_D @ C1092MAPC_D2 @ sq)
      C1092MAR_ROTATED_FRAME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c1092psa_frame; C1092PSA_INSIDE_TRANSLATED]; ALL_TAC] THEN
    REWRITE_TAC[c1092psa_frame; C1092PSA_INSIDE_TRANSLATED] THEN
    DISCH_THEN(MP_TAC o SPECL [`--(&1 / &2)`; `&0`]) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    UNDISCH_TAC `c1092mapc_crosspoint d10 d20 e10 e20 l` THEN
    REWRITE_TAC[c1092mapc_crosspoint] THEN MESON_TAC[]);;

(* Lean: AllCrosspoints.rotated *)
let C1092MAPC_ALLCROSSPOINTS_ROTATED = prove
 (parse_term (Printf.sprintf "!%s i d1 d2 e1 e2. %s /\\ c1092mapc_allCrosspoints %s /\\ i < 4 /\\ %s
      ==> c1092mapc_allCrosspoints d1 d2 e1 e2 l"
    C1092MAPC_P C1092AE_HYP C1092MAPC_P (c1092mapc_pks `i:num` C1092MAPC_V4 C1092MAPC_D)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [c1092mapc_allCrosspoints] THEN
  MAP_EVERY X_GEN_TAC (`j:num` :: C1092MAPC_D2) THEN STRIP_TAC THEN
  c1092mapc_choose_tac (c1092mapc_el C1092MAPC_SUM) C1092MAPC_V4 C1092MAPC_D0 THEN
  MATCH_MP_TAC (SPECL (C1092MAPC_V @ [`i:num`; `j:num`] @ C1092MAPC_D0 @ C1092MAPC_D @ C1092MAPC_D2)
    C1092MAPC_CROSSPOINT_COMPOSED) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL (C1092MAPC_SUM :: C1092MAPC_D0) o REWRITE_RULE[c1092mapc_allCrosspoints] o
    check (c1092mpapo_head `c1092mapc_allCrosspoints`)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092mar_addSector; MOD_LT_EQ; ARITH]);;

(* Lean: next_crosspoint *)
let C1092MAPC_NEXT_CROSSPOINT = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2. %s /\\ %s /\\ c1092mapc_crosspoint d1 d2 e1 e2 l ==> %s"
    C1092MAPC_P C1092AE_HYP C1092MAR_DPK1 (c1092mppe_in 5 "&2" "&3 / &2")),
  REPEAT GEN_TAC THEN REWRITE_TAC C1092MPAPO_ROT_ELS THEN STRIP_TAC THEN
  UNDISCH_TAC `c1092mapc_crosspoint d1 d2 e1 e2 l` THEN REWRITE_TAC[c1092mapc_crosspoint] THEN
  c1092mar_pull_tac C1092MAPC_V4 C1092MAPC_D `(true,true,false)` [4]);;

(* Lean: positive_propagation_of_scalars *)
let C1092MAPC_POSITIVE_PROPAGATION_OF_SCALARS = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD.
      c1092mapc_scalarProof /\\ %s /\\ ~c1092mapc_forward %s /\\ %s /\\ %s /\\ %s /\\
      c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ c977cc_normal cD sD /\\ &0 < sD /\\ %s
      ==> c1092mapc_crosspoint %s"
    C1092MAPC_P C1092MPAPO_HYPS C1092MAPC_P C1092MAR_CHYPS C1092MAR_DPK1 C1092MAR_DSQ
    (c1092mppe_in 5 "&2" "&3 / &2") C1092MAPC_P),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mapc_forward; c1092mapc_crosspoint] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAPC_V @ C1092MAPC_CV) C1092MABO_ACTUAL_MISSING_CROSSPOINT_CAPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092MABO_STEEP_SINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAPC_V @ C1092MAPC_CV @ C1092MAPC_D @ C1092MAPC_DV) C1092SPTSA_ACTUAL_INPUT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MAPC_CV @ C1092MAR_E @ C1092SPTSA_B) C1092SPTG_IMPOSSIBLE_OF_MODES) THEN
  ASM_REWRITE_TAC[c1092psa_unit 9; c1092psa_pos ()] THEN
  UNDISCH_TAC `c1092mapc_scalarProof` THEN REWRITE_TAC[c1092mapc_scalarProof; IMP_IMP] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* Lean: backward_cycle (private) *)
let C1092MAPC_BACKWARD_CYCLE = prove
 (`forall P. (exists i. i < 4 /\ P i) /\ (forall i. i < 4 /\ P (c1092mar_addSector i 1) ==> P i)
       ==> forall i. i < 4 ==> P i`,
  GEN_TAC THEN REWRITE_TAC[c1092mar_addSector] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(P 1 ==> P 0) /\ (P 2 ==> P 1) /\ (P 3 ==> P 2) /\ (P 0 ==> P (3:num))`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `P 0 /\ P 1 /\ P 2 /\ P (3:num)` STRIP_ASSUME_TAC THENL
   [C1092WP_ENUM_TAC `i:num` 4 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN C1092WP_ENUM_TAC `k:num` 4 THEN ASM_REWRITE_TAC[]);;

(* Lean: seed_exists (private) *)
let C1092MAPC_SEED_EXISTS =
  let one k =
    let ks = string_of_int k in
    let dk = c1092mpapo_d4 ks and g = el k C1092MPAPO_ROTS in
    c1092mpapo_rot_tac ks k THEN
    FIRST_ASSUM(MP_TAC o SPECL (mk_small_numeral k :: dk) o
      check (fun th -> is_forall (concl th) && can (find_term ((=) `c1092mpapo_rotation`)) (concl th))) THEN
    REWRITE_TAC(ARITH :: C1092MPAPO_ROT_ELS) THEN ASM_REWRITE_TAC[c1092mapc_forward] THEN
    c1092mpapo_pull_tac dk g [4] in
  prove
   (parse_term (Printf.sprintf "!%s. %s /\\ c1092mapc_positiveFrames %s
        ==> ?i d1 d2 e1 e2. i < 4 /\\ %s /\\ c1092mapc_forward d1 d2 e1 e2 l"
      C1092MAPC_P C1092MPAPO_HYPS C1092MAPC_P (c1092mapc_pks `i:num` C1092MAPC_V4 C1092MAPC_D)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    MATCH_MP_TAC (SPECL C1092MAPC_V C1092MPAPO_ALL_MISSING_POSITIVE_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[c1092mpapo_missingForward] THEN REPEAT CONJ_TAC THENL (map one [0; 1; 2; 3]);
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      c1092mapc_frame_tac C1092MAPC_V `i:num` C1092MAPC_D C1092MAPC_CV THEN
      MAP_EVERY EXISTS_TAC C1092MAPC_CV THEN ASM_REWRITE_TAC[]]);;

(* Lean: all_crosspoints_of_scalars *)
let C1092MAPC_ALL_CROSSPOINTS_OF_SCALARS = prove
 (parse_term (Printf.sprintf "!%s. c1092mapc_scalarProof /\\ %s /\\ c1092mapc_positiveFrames %s
      ==> c1092mapc_allCrosspoints %s" C1092MAPC_P C1092MPAPO_HYPS C1092MAPC_P C1092MAPC_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC (mk_abs(`i:num`, list_mk_forall(C1092MAPC_D,
      mk_imp(c1092mapc_pk `i:num` C1092MAPC_V4 C1092MAPC_D, `c1092mapc_crosspoint d1 d2 e1 e2 l`))))
    C1092MAPC_BACKWARD_CYCLE) THEN
  BETA_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (c ==> d) ==> ((a /\ b ==> c) ==> d)`) THEN REPEAT CONJ_TAC THENL
   [(* the retaining seed *)
    MP_TAC(SPECL C1092MAPC_V C1092MAPC_SEED_EXISTS) THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(c1092mapc_chain (`i:num` :: C1092MAPC_D) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `c1092mapc_crosspoint d1 d2 e1 e2 l` ASSUME_TAC THENL
     [C1092MPAPO_DGEN_TAC THEN
      c1092mapc_frame_tac C1092MAPC_V `i:num` C1092MAPC_D C1092MAPC_CV THEN
      RULE_ASSUM_TAC(REWRITE_RULE[c1092mapc_forward]) THEN REWRITE_TAC[c1092mapc_crosspoint] THEN
      MATCH_MP_TAC (SPECL (C1092MAPC_D5 @ C1092MAPC_CV) C1092MAR_FORWARD_CROSSPOINT) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x1:num->real`; `x2:num->real`; `x3:num->real`; `x4:num->real`] THEN
    ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    (* the backward step *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC C1092MAPC_D THEN DISCH_TAC THEN
    C1092MPAPO_DGEN_TAC THEN
    c1092mapc_frame_tac C1092MAPC_V `i:num` C1092MAPC_D C1092MAPC_CV THEN
    ASM_CASES_TAC `c1092mapc_forward d1 d2 e1 e2 l` THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[c1092mapc_forward]) THEN REWRITE_TAC[c1092mapc_crosspoint] THEN
      MATCH_MP_TAC (SPECL (C1092MAPC_D5 @ C1092MAPC_CV) C1092MAR_FORWARD_CROSSPOINT) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    c1092mapc_choose_tac (c1092mapc_el `c1092mar_addSector i 1`) C1092MAPC_V4 C1092MAPC_D0 THEN
    c1092mapc_choose_tac (c1092mapc_el `1`) C1092MAPC_D C1092MAPC_D2 THEN
    c1092mapc_frame_tac C1092MAPC_V `c1092mar_addSector i 1` C1092MAPC_D0 C1092MAPC_DV THEN
    MP_TAC(SPECL (C1092MAPC_V @ [`i:num`; `1`] @ C1092MAPC_D0 @ C1092MAPC_D @ C1092MAPC_D2 @ C1092MAPC_DV)
      C1092MAR_ROTATED_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL C1092MAPC_D0 o
      check (fun th -> is_forall (concl th) && can (find_term ((=) `c1092mar_addSector i 1`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL (C1092MAPC_V @ [`i:num`; `1`] @ C1092MAPC_D0 @ C1092MAPC_D @ C1092MAPC_D2)
      C1092MAPC_CROSSPOINT_COMPOSED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
    MP_TAC(SPECL (C1092MAPC_D5 @ C1092MAPC_D2) C1092MAPC_NEXT_CROSSPOINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC (SPECL (C1092MAPC_D5 @ C1092MAPC_CV @ C1092MAPC_D2 @ C1092MAPC_DV)
      C1092MAPC_POSITIVE_PROPAGATION_OF_SCALARS) THEN
    ASM_REWRITE_TAC[];
    (* conclusion *)
    REWRITE_TAC[c1092mapc_allCrosspoints] THEN MESON_TAC[]]);;

let C1092MAPC_HYPS3 = Printf.sprintf "%s /\\ c1092mapc_positiveFrames %s /\\ c1092mapc_allCrosspoints %s"
  C1092MPAPO_HYPS C1092MAPC_P C1092MAPC_P;;

(* Lean: bottom_origin *)
let C1092MAPC_BOTTOM_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092MAPC_P C1092MAPC_HYPS3 (c1092mppe_in 9 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mapc_choose_tac (c1092mapc_el `0`) C1092MAPC_V4 C1092MAPC_D0 THEN
  c1092mapc_frame_tac C1092MAPC_V `0` C1092MAPC_D0 C1092MAPC_CV THEN
  MP_TAC(SPECL (C1092MAPC_V @ C1092MAPC_D0 @ C1092MAPC_CV) C1092MAR_ORIGINAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 4 "&87 / &50" "&2")) THENL
   [c1092mapc_choose_tac (c1092mapc_el `3`) C1092MAPC_V4 C1092MAPC_D THEN
    c1092mapc_frame_tac C1092MAPC_V `3` C1092MAPC_D C1092MAPC_WV THEN
    c1092mapc_choose_tac (c1092mapc_el `1`) C1092MAPC_V4 C1092MAPC_D1 THEN
    FIRST_ASSUM(MP_TAC o SPECL (`1` :: C1092MAPC_D1) o REWRITE_RULE[c1092mapc_allCrosspoints] o
      check (c1092mpapo_head `c1092mapc_allCrosspoints`)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
    MP_TAC(SPECL (C1092MAPC_V @ C1092MAPC_D1) C1092MAPC_NEXT_CROSSPOINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL (C1092MAPC_V @ C1092MAPC_CV @ C1092MAPC_D @ C1092MAPC_WV) C1092MAR_RETAINING_HALFPOINT_ORIGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN C1092MPAPO_ORD_TAC THEN
    MATCH_MP_TAC (SPECL C1092MAPC_V C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[]]);;

(* Lean: left_origin *)
let C1092MAPC_LEFT_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s. %s ==> %s" C1092MAPC_P C1092MAPC_HYPS3 (c1092mppe_in 8 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mapc_choose_tac (c1092mapc_el `3`) C1092MAPC_V4 C1092MAPC_D THEN
  c1092mapc_facts_tac C1092MAPC_V4 C1092MAPC_D `3` THEN
  MP_TAC(SPECL (C1092MAPC_V @ [`3`] @ C1092MAPC_D) C1092MAPC_POSITIVEFRAMES_ROTATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAPC_V @ [`3`] @ C1092MAPC_D) C1092MAPC_ALLCROSSPOINTS_ROTATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
  MP_TAC(SPECL C1092MAPC_D5 C1092MAPC_BOTTOM_ORIGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  c1092mapc_lit_tac `3` C1092MAPC_V4 C1092MAPC_D THEN
  c1092mar_pull_tac C1092MAPC_V4 C1092MAPC_D `(true,false,true)` [9]);;

(* Lean: impossible_of_scalars *)
let C1092MAPC_IMPOSSIBLE_OF_SCALARS = prove
 (parse_term (Printf.sprintf "!%s. c1092mapc_scalarProof /\\ %s /\\ c1092mapc_positiveFrames %s ==> F"
    C1092MAPC_P C1092MPAPO_HYPS C1092MAPC_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092MAPC_V C1092MAPC_ALL_CROSSPOINTS_OF_SCALARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MATCH_MP_TAC (SPECL C1092MAPC_V C1092MPAPO_IMPOSSIBLE_OF_POSITIVE_ENTRANCE) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC (`i:num` :: C1092MAPC_D) THEN STRIP_TAC THEN
  C1092MPAPO_DGEN_TAC THEN
  MP_TAC(SPECL (C1092MAPC_V @ [`i:num`] @ C1092MAPC_D) C1092MAPC_POSITIVEFRAMES_ROTATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAPC_V @ [`i:num`] @ C1092MAPC_D) C1092MAPC_ALLCROSSPOINTS_ROTATED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  c1092mapc_frame_tac C1092MAPC_V `i:num` C1092MAPC_D C1092MAPC_CV THEN
  c1092mapc_choose_tac (c1092mapc_el `3`) C1092MAPC_D C1092MAPC_D3 THEN
  c1092mapc_frame_tac C1092MAPC_D5 `3` C1092MAPC_D3 C1092MAPC_WV THEN
  c1092mapc_choose_tac (c1092mapc_el `1`) C1092MAPC_D C1092MAPC_D1 THEN
  FIRST_ASSUM(MP_TAC o SPECL (`1` :: C1092MAPC_D1) o REWRITE_RULE[c1092mapc_allCrosspoints] o
    check (fun th -> concl th = list_mk_comb(`c1092mapc_allCrosspoints`, C1092MAPC_D5))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAPC_D5 @ C1092MAPC_D1) C1092MAPC_NEXT_CROSSPOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL C1092MAPC_D5 C1092MAPC_LEFT_ORIGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC C1092MAPC_CV THEN ASM_REWRITE_TAC[c1092mpapo_entrance] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL (C1092MAPC_D5 @ C1092MAPC_CV @ C1092MAPC_D3 @ C1092MAPC_WV) C1092MAR_RETAINING_SHALLOW) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[c1092pad_shallow] THEN STRIP_TAC THEN ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

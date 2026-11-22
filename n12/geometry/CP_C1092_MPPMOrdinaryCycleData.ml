(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOrdinaryCycleData.lean               *)
(* (N12Compact.C1092MPPMOrdinaryCycle; Lean header: "Source only,            *)
(* uncompiled").  A canonical frame for each of the four actual ordinary     *)
(* central owners and the signed-cycle rules.  Conventions of                *)
(* CP_C1092_MPPMActualCrosspoints.ml / MPPMAllNonpositiveActual.ml: owners p *)
(* i at mask EL i c1092wc_code, side l; WallContext p mppm C1092MPPE_CTX;    *)
(* Ordinary c1092mpapo_ordinary; ActualFrame c1092psa_frame (OpenSquare      *)
(* invariants explicit); (rotation i).pullPacking p = (d1,d2,e1,e2) with     *)
(* c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2), i < 4; *)
(* addSector c1092mar_addSector; Forward / Crosspoint c1092mapc_forward /    *)
(* c1092mapc_crosspoint.                                                     *)
(* Frames p (square : Fin 4 -> OpenSquare) is the predicate c1092mocd_frames *)
(* over cc cs cu cv ca : num->real (= C1092MACR_FRAMES); Positive d i is     *)
(* `&0 < cs i`; Retains p i is c1092mocd_retains (Forward of the pulled      *)
(* packing).  Frames.rotated has the squares (\j. cc (addSector i j)) ...    *)
(* Used: rotated_frame C1092MAR_ROTATED_FRAME, forward_composed(_iff) /      *)
(* next_forward_iff / positive_crosspoints C1092MACR_*, crosspoint_composed /*)
(* next_crosspoint C1092MAPC_*, exists_canonical_frame                       *)
(* C1092PSA_EXISTS_CANONICAL_FRAME, rotation_context / Ordinary.rotated      *)
(* C1092MPAPO_*, successor_retaining_impossible C1092NMPA_*,                 *)
(* negative_missing_successor_missing_impossible C1092PMLC_*,                *)
(* retaining_edge_impossible C1092NOPA_*, adjacent_missing_impossible        *)
(* C1092MNCA_*, actual_three_retaining_impossible C1092ANPA_*, the one-      *)
(* positive entrances C1092OPAC_*.  Tag C1092MOCD_.                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositiveActual.ml";;
needs "n12/geometry/CP_C1092_MPPMOnePositiveActual.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeMissingPositiveActual.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveActual.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCentersActual.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveMissingLeftCenter.ml";;
needs "n12/geometry/CP_C1092_MPPMActualCrosspoints.ml";;

let C1092MOCD_V = C1092MAR_V;;
let C1092MOCD_V4 = C1092MPAPO_V4;;
let C1092MOCD_D = C1092MAR_D;;
let C1092MOCD_F4 = C1092MACR_F4;;
let C1092MOCD_FR = "c1092mocd_frames c1 c2 a b l cc cs cu cv ca";;
let C1092MOCD_HYPS = C1092MPAPO_HYPS;;
let c1092mocd_sum j = mk_comb(mk_comb(`c1092mar_addSector`, `i:num`), mk_small_numeral j);;
let c1092mocd_sums j = Printf.sprintf "c1092mar_addSector i %d" j;;
let c1092mocd_p j = c1092mpapo_d4 ("p" ^ string_of_int j);;
let c1092mocd_q j = c1092mpapo_d4 ("q" ^ string_of_int j);;
let c1092mocd_din = c1092mpapo_din;;

(* Lean: Frames (structure) *)
let c1092mocd_frames = new_definition (parse_term (Printf.sprintf
  "c1092mocd_frames (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
     (cc:num->real) (cs:num->real) (cu:num->real) (cv:num->real) (ca:num->real) <=> %s"
  C1092MACR_FRAMES));;

(* Lean: Retains (definition) *)
let c1092mocd_retains = new_definition
 `c1092mocd_retains (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (i:num) <=>
    forall d1 d2 e1 e2. c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2)
      ==> c1092mapc_forward d1 d2 e1 e2 l`;;

let C1092MOCD_ADD_LT = prove
 (`forall i j. c1092mar_addSector i j < 4`,
  REWRITE_TAC[c1092mar_addSector; MOD_LT_EQ; ARITH]);;

(* Retains at a named pulled packing *)
let C1092MOCD_RETAINS_AT = prove
 (`forall c1 c2 a b l i d1 d2 e1 e2.
     c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2)
     ==> (c1092mocd_retains c1 c2 a b l i <=> c1092mapc_forward d1 d2 e1 e2 l)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[c1092mocd_retains] THEN EQ_TAC THENL
   [DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]]);;

(* Lean: Frames.positive_normal *)
let C1092MOCD_FRAMES_POSITIVE_NORMAL = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ i < 4 /\\ &0 < cs i ==> c977cc_normal (cc i) (cs i)"
    C1092AE_P C1092MOCD_FR),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mocd_frames] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
    not (can (find_term ((=) `d1:num->real`)) (concl th))))) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM_REAL_ARITH_TAC);;

(* Lean: Frames.nonpositive_normal *)
let C1092MOCD_FRAMES_NONPOSITIVE_NORMAL = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ i < 4 /\\ ~(&0 < cs i) ==> c977cc_normal (cc i) (--(cs i))"
    C1092AE_P C1092MOCD_FR),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mocd_frames] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall (concl th) &&
    not (can (find_term ((=) `d1:num->real`)) (concl th))))) THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN REPEAT STRIP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: Frames.rotated *)
let C1092MOCD_FRAMES_ROTATED = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i d1 d2 e1 e2. %s /\\ %s /\\ i < 4 /\\ %s
      ==> c1092mocd_frames d1 d2 e1 e2 l (\\j. cc (c1092mar_addSector i j)) (\\j. cs (c1092mar_addSector i j))
            (\\j. cu (c1092mar_addSector i j)) (\\j. cv (c1092mar_addSector i j)) (\\j. ca (c1092mar_addSector i j))"
    C1092AE_P C1092AE_HYP C1092MOCD_FR c1092mpapo_dpk),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mocd_frames] THEN STRIP_TAC THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[C1092MOCD_ADD_LT]; ALL_TAC; ASM_SIMP_TAC[C1092MOCD_ADD_LT]] THEN
  MAP_EVERY X_GEN_TAC (`j:num` :: C1092MAR_D2) THEN STRIP_TAC THEN
  c1092mapc_choose_tac (c1092mapc_el `c1092mar_addSector i j`) C1092MOCD_V4 C1092MAR_D0 THEN
  MATCH_MP_TAC (SPECL (C1092MOCD_V @ [`i:num`; `j:num`] @ C1092MAR_D0 @ C1092MOCD_D @ C1092MAR_D2 @
    c1092macr_at `c1092mar_addSector i j`) C1092MAR_ROTATED_FRAME) THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[C1092MOCD_ADD_LT]);;

(* Lean: Frames.exists *)
let C1092MOCD_FRAMES_EXISTS = prove
 (parse_term (Printf.sprintf "forall %s. NPACK c1 c2 a b l ==> exists cc cs cu cv ca. %s" C1092AE_P C1092MOCD_FR),
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `forall i:num. exists cC sC uC vC aC. cC * cC + sC * sC = &1 /\ &0 < aC /\
      (forall d1 d2 e1 e2. c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2)
         ==> c1092psa_frame d1 d2 e1 e2 l cC sC uC vC aC) /\ abs sC <= cC`
    MP_TAC THENL
   [GEN_TAC THEN
    c1092mapc_choose_tac (c1092mapc_el `i:num`) C1092MOCD_V4 C1092MOCD_D THEN
    SUBGOAL_THEN `NPACK d1 d2 e1 e2 l` ASSUME_TAC THENL
     [MATCH_MP_TAC C1092OT_NPACK THEN
      MAP_EVERY EXISTS_TAC (`EL i c1092mpapo_rotation` :: C1092MOCD_V4) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP C1092PSA_EXISTS_CANONICAL_FRAME) THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN ASM_REWRITE_TAC[PAIR_EQ] THEN
    DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; c1092mocd_frames] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MESON_TAC[]);;

(* retaining at a composed sector, read in the pulled packing *)
let C1092MOCD_RETAINS_COMPOSED = prove
 (parse_term (Printf.sprintf "forall %s i j d1 d2 e1 e2 d12 d22 e12 e22. %s /\\ i < 4 /\\ j < 4 /\\ %s /\\ %s
      ==> (c1092mocd_retains c1 c2 a b l (c1092mar_addSector i j) <=> c1092mapc_forward d12 d22 e12 e22 l)"
    C1092AE_P C1092AE_HYP c1092mpapo_dpk (c1092mapc_pks `j:num` C1092MOCD_D C1092MAR_D2)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mapc_choose_tac (c1092mapc_el `c1092mar_addSector i j`) C1092MOCD_V4 C1092MAR_D0 THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`c1092mar_addSector i j`] @ C1092MAR_D0) C1092MOCD_RETAINS_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MOCD_V @ [`i:num`; `j:num`] @ C1092MAR_D0 @ C1092MOCD_D @ C1092MAR_D2)
    C1092MACR_FORWARD_COMPOSED_IFF) THEN
  ASM_REWRITE_TAC[]);;

let C1092MOCD_PK_HYPS = Printf.sprintf "%s /\\ i < 4 /\\ %s" C1092AE_HYP c1092mpapo_dpk;;

(* pulled-packing facts NPACK / IMAGE of d, and the composed packing q = pk j d *)
let c1092mocd_q_tac j =
  c1092mar_pk_facts_tac (c1092mapc_el `i:num`) C1092MOCD_V4 C1092MOCD_D THEN
  c1092mapc_choose_tac (c1092mapc_el (mk_small_numeral j)) C1092MOCD_D C1092MAR_D2 THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`; mk_small_numeral j] @ C1092MOCD_D @ C1092MAR_D2) C1092MOCD_RETAINS_COMPOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_THEN SUBST1_TAC];;

(* the owner equivalence of Forward of the packing pk j d *)
let C1092MOCD_NEXT_IFF = prove
 (parse_term (Printf.sprintf "forall %s i d1 d2 e1 e2. %s
      ==> (c1092mocd_retains c1 c2 a b l (c1092mar_addSector i 1) <=> %s)"
    C1092AE_P C1092MOCD_PK_HYPS (c1092mocd_din 5 "&2" "&87 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_q_tac 1 THEN
  MP_TAC(SPECL (C1092MANH_D5 @ C1092MAR_D2) C1092MACR_NEXT_FORWARD_IFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

let C1092MOCD_PREVIOUS_IFF = prove
 (parse_term (Printf.sprintf "forall %s i d1 d2 e1 e2. %s
      ==> (c1092mocd_retains c1 c2 a b l (c1092mar_addSector i 3) <=> %s)"
    C1092AE_P C1092MOCD_PK_HYPS (c1092mocd_din 7 "&2" "&113 / &50")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_q_tac 3 THEN
  RULE_ASSUM_TAC(REWRITE_RULE C1092MPAPO_ROT_ELS) THEN
  REWRITE_TAC[c1092mapc_forward] THEN
  c1092mar_pull_tac C1092MOCD_D C1092MAR_D2 `(true,false,true)` [4]);;

(* Lean: next_retained *)
let C1092MOCD_NEXT_RETAINED = prove
 (parse_term (Printf.sprintf "forall %s i d1 d2 e1 e2. %s /\\ c1092mocd_retains c1 c2 a b l (c1092mar_addSector i 1) ==> %s"
    C1092AE_P C1092MOCD_PK_HYPS (c1092mocd_din 5 "&2" "&87 / &50")),
  MESON_TAC[C1092MOCD_NEXT_IFF]);;

(* Lean: next_missing *)
let C1092MOCD_NEXT_MISSING = prove
 (parse_term (Printf.sprintf "forall %s i d1 d2 e1 e2. %s /\\ ~c1092mocd_retains c1 c2 a b l (c1092mar_addSector i 1) ==> ~%s"
    C1092AE_P C1092MOCD_PK_HYPS (c1092mocd_din 5 "&2" "&87 / &50")),
  MESON_TAC[C1092MOCD_NEXT_IFF]);;

(* Lean: previous_missing *)
let C1092MOCD_PREVIOUS_MISSING = prove
 (parse_term (Printf.sprintf "forall %s i d1 d2 e1 e2. %s /\\ ~c1092mocd_retains c1 c2 a b l (c1092mar_addSector i 3) ==> ~%s"
    C1092AE_P C1092MOCD_PK_HYPS (c1092mocd_din 7 "&2" "&113 / &50")),
  MESON_TAC[C1092MOCD_PREVIOUS_IFF]);;

(* crosspoint of pk (addSector i j) p, read as crosspoint of pk j d *)
let c1092mocd_cross_tac j =
  c1092mar_pk_facts_tac (c1092mapc_el `i:num`) C1092MOCD_V4 C1092MOCD_D THEN
  c1092mapc_choose_tac (c1092mapc_el (mk_small_numeral j)) C1092MOCD_D C1092MAR_D2 THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`; mk_small_numeral j] @ C1092MAR_D0 @ C1092MOCD_D @ C1092MAR_D2)
    C1092MAPC_CROSSPOINT_COMPOSED) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC];;

(* Lean: next_point *)
let C1092MOCD_NEXT_POINT = prove
 (parse_term (Printf.sprintf "forall %s i d1 d2 e1 e2 d10 d20 e10 e20. %s /\\ %s /\\ c1092mapc_crosspoint d10 d20 e10 e20 l ==> %s"
    C1092AE_P C1092MOCD_PK_HYPS (c1092mapc_pks `c1092mar_addSector i 1` C1092MOCD_V4 C1092MAR_D0)
    (c1092mocd_din 5 "&2" "&3 / &2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_cross_tac 1 THEN
  MATCH_MP_TAC (SPECL (C1092MANH_D5 @ C1092MAR_D2) C1092MAPC_NEXT_CROSSPOINT) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: opposite_point *)
let C1092MOCD_OPPOSITE_POINT = prove
 (parse_term (Printf.sprintf "forall %s i d1 d2 e1 e2 d10 d20 e10 e20. %s /\\ %s /\\ c1092mapc_crosspoint d10 d20 e10 e20 l ==> %s"
    C1092AE_P C1092MOCD_PK_HYPS (c1092mapc_pks `c1092mar_addSector i 2` C1092MOCD_V4 C1092MAR_D0)
    (c1092mocd_din 6 "&5 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_cross_tac 2 THEN
  RULE_ASSUM_TAC(REWRITE_RULE C1092MPAPO_ROT_ELS) THEN
  UNDISCH_TAC `c1092mapc_crosspoint d12 d22 e12 e22 l` THEN REWRITE_TAC[c1092mapc_crosspoint] THEN
  c1092mar_pull_tac C1092MOCD_D C1092MAR_D2 `(false,true,true)` [4]);;

(* Lean: Frames.positive_points *)
let C1092MOCD_FRAMES_POSITIVE_POINTS = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca. %s /\\ %s ==> %s"
    C1092AE_P C1092MOCD_HYPS C1092MOCD_FR C1092MACR_CONCL),
  REWRITE_TAC[c1092mocd_frames] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC (SPECL (C1092MOCD_V @ C1092MOCD_F4) C1092MACR_POSITIVE_CROSSPOINTS) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Setup for the signed-cycle rules: d = pk i p with its facts and frame;    *)
(* for a sector j: p_j = pk (addSector i j) p, q_j = pk j d with the frame   *)
(* of the square at addSector i j in q_j.                                    *)
(* ------------------------------------------------------------------------- *)

let c1092mocd_k j = c1092mocd_sum j;;

let c1092mocd_normal_tac k positive =
  MP_TAC(SPECL (C1092MOCD_V @ C1092MOCD_F4 @ [k])
    (if positive then C1092MOCD_FRAMES_POSITIVE_NORMAL else C1092MOCD_FRAMES_NONPOSITIVE_NORMAL)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[C1092MOCD_ADD_LT]; DISCH_TAC];;

let c1092mocd_base_tac =
  c1092mapc_choose_tac (c1092mapc_el `i:num`) C1092MOCD_V4 C1092MOCD_D THEN
  c1092mapc_facts_tac C1092MOCD_V4 C1092MOCD_D `i:num` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mocd_frames] o check (c1092mpapo_head `c1092mocd_frames`)) THEN
  c1092macr_inst_tac `i:num` THEN c1092macr_frame_tac `i:num` C1092MOCD_D;;

let c1092mocd_sector_tac j =
  let k = c1092mocd_k j and pj = c1092mocd_p j and qj = c1092mocd_q j in
  c1092mapc_choose_tac (c1092mapc_el k) C1092MOCD_V4 pj THEN
  c1092mapc_choose_tac (c1092mapc_el (mk_small_numeral j)) C1092MOCD_D qj THEN
  c1092macr_inst_tac k THEN c1092macr_frame_tac k pj THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`; mk_small_numeral j] @ pj @ C1092MOCD_D @ qj @ c1092macr_at k)
    C1092MAR_ROTATED_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH; C1092MOCD_ADD_LT]; DISCH_TAC];;

(* rewrite the Retains assumptions of sectors i, i+1, i+3, i+j into owner facts *)
let c1092mocd_retains_tac js =
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`] @ C1092MOCD_D) C1092MOCD_RETAINS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; c1092mapc_forward]))] THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`] @ C1092MOCD_D) C1092MOCD_NEXT_IFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`] @ C1092MOCD_D) C1092MOCD_PREVIOUS_IFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  MAP_EVERY (fun j ->
    MP_TAC(SPECL (C1092MOCD_V @ [`i:num`; mk_small_numeral j] @ C1092MOCD_D @ c1092mocd_q j) C1092MOCD_RETAINS_COMPOSED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))]) js;;

let c1092mocd_choose_p j =
  c1092mapc_choose_tac (c1092mapc_el (c1092mocd_k j)) C1092MOCD_V4 (c1092mocd_p j);;

(* positive sector j of p gives the crosspoint of p_j *)
let c1092mocd_point_tac j =
  MP_TAC(SPECL (C1092MOCD_V @ C1092MOCD_F4) C1092MOCD_FRAMES_POSITIVE_POINTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL (c1092mocd_k j :: c1092mocd_p j)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[C1092MOCD_ADD_LT]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`] @ C1092MOCD_D @ c1092mocd_p j)
    (if j = 1 then C1092MOCD_NEXT_POINT else C1092MOCD_OPPOSITE_POINT)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC];;

let c1092mocd_apply th sqs =
  MATCH_MP_TAC (SPECL (C1092MANH_D5 @ c1092macr_at `i:num` @ List.concat sqs) th) THEN
  ASM_REWRITE_TAC[];;
let c1092mocd_sq j = c1092mocd_q j @ c1092macr_at (c1092mocd_k j);;

let C1092MOCD_CORE = Printf.sprintf "%s /\\ %s /\\ i < 4" C1092MOCD_HYPS C1092MOCD_FR;;
let c1092mocd_pos j = if j = 0 then "&0 < cs i" else Printf.sprintf "&0 < cs (%s)" (c1092mocd_sums j);;
let c1092mocd_ret j = if j = 0 then "c1092mocd_retains c1 c2 a b l i"
  else Printf.sprintf "c1092mocd_retains c1 c2 a b l (%s)" (c1092mocd_sums j);;

(* Lean: signed_edge *)
let C1092MOCD_SIGNED_EDGE = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ ~(%s) /\\ %s ==> %s /\\ ~%s"
    C1092AE_P C1092MOCD_CORE (c1092mocd_pos 0) (c1092mocd_pos 1) (c1092mocd_ret 0) (c1092mocd_ret 1)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_base_tac THEN c1092mocd_sector_tac 1 THEN
  c1092mocd_normal_tac `i:num` false THEN c1092mocd_normal_tac (c1092mocd_k 1) true THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`] @ C1092MOCD_D) C1092MOCD_RETAINS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`] @ C1092MOCD_D) C1092MOCD_NEXT_IFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[c1092mapc_forward] THEN
  ASM_CASES_TAC (parse_term (c1092mocd_din 4 "&87 / &50" "&2")) THEN ASM_REWRITE_TAC[] THENL
   [DISCH_TAC THEN c1092mocd_apply C1092NOPA_RETAINING_EDGE_IMPOSSIBLE [c1092mocd_sq 1];
    ASM_CASES_TAC (parse_term (c1092mocd_din 5 "&2" "&87 / &50")) THENL
     [c1092mocd_apply C1092NMPA_SUCCESSOR_RETAINING_IMPOSSIBLE [c1092mocd_sq 1];
      c1092mocd_apply C1092PMLC_NEGATIVE_MISSING_SUCCESSOR_MISSING_IMPOSSIBLE [c1092mocd_sq 1]]]);;

(* Lean: adjacent_missing *)
let C1092MOCD_ADJACENT_MISSING = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ ~(%s) /\\ ~(%s) /\\ ~%s /\\ ~%s ==> false"
    C1092AE_P C1092MOCD_CORE (c1092mocd_pos 0) (c1092mocd_pos 1) (c1092mocd_ret 0) (c1092mocd_ret 1)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_base_tac THEN c1092mocd_sector_tac 1 THEN
  c1092mocd_normal_tac `i:num` false THEN c1092mocd_normal_tac (c1092mocd_k 1) false THEN
  c1092mocd_retains_tac [] THEN
  c1092mocd_apply C1092MNCA_ADJACENT_MISSING_IMPOSSIBLE [c1092mocd_sq 1]);;

(* Lean: three_retaining *)
let C1092MOCD_THREE_RETAINING = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ ~(%s) /\\ ~(%s) /\\ ~(%s) /\\ %s /\\ %s /\\ %s ==> false"
    C1092AE_P C1092MOCD_CORE (c1092mocd_pos 0) (c1092mocd_pos 1) (c1092mocd_pos 2)
    (c1092mocd_ret 0) (c1092mocd_ret 1) (c1092mocd_ret 2)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_base_tac THEN
  c1092mocd_sector_tac 1 THEN c1092mocd_sector_tac 2 THEN
  c1092mocd_normal_tac `i:num` false THEN c1092mocd_normal_tac (c1092mocd_k 1) false THEN
  c1092mocd_normal_tac (c1092mocd_k 2) false THEN
  MAP_EVERY (fun j ->
    MP_TAC(SPECL (C1092MOCD_V @ [`i:num`; mk_small_numeral j] @ C1092MOCD_D @ c1092mocd_q j) C1092MOCD_RETAINS_COMPOSED) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))])
    [1; 2] THEN
  MP_TAC(SPECL (C1092MOCD_V @ [`i:num`] @ C1092MOCD_D) C1092MOCD_RETAINS_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))] THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[c1092mapc_forward] o
    check (fun th -> concl th = `c1092mapc_forward d1 d2 e1 e2 l`)) THEN
  c1092mocd_apply C1092ANPA_ACTUAL_THREE_RETAINING_IMPOSSIBLE [c1092mocd_sq 1; c1092mocd_sq 2]);;

(* Lean: positive_sandwich *)
let C1092MOCD_POSITIVE_SANDWICH = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ %s /\\ ~(%s) /\\ %s /\\ %s /\\ ~%s ==> false"
    C1092AE_P C1092MOCD_CORE (c1092mocd_pos 3) (c1092mocd_pos 0) (c1092mocd_pos 1)
    (c1092mocd_ret 0) (c1092mocd_ret 1)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_base_tac THEN
  c1092mocd_sector_tac 1 THEN c1092mocd_sector_tac 3 THEN
  c1092mocd_normal_tac `i:num` false THEN c1092mocd_normal_tac (c1092mocd_k 1) true THEN
  c1092mocd_normal_tac (c1092mocd_k 3) true THEN
  c1092mocd_point_tac 1 THEN c1092mocd_retains_tac [] THEN
  c1092mocd_apply C1092OPAC_POSITIVE_SANDWICH_IMPOSSIBLE [c1092mocd_sq 3; c1092mocd_sq 1]);;

(* Lean: missing_before_positive *)
let C1092MOCD_MISSING_BEFORE_POSITIVE = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ ~(%s) /\\ ~%s /\\ ~(%s) /\\ %s /\\ %s /\\ ~%s ==> false"
    C1092AE_P C1092MOCD_CORE (c1092mocd_pos 3) (c1092mocd_ret 3) (c1092mocd_pos 0) (c1092mocd_ret 0)
    (c1092mocd_pos 1) (c1092mocd_ret 1)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_base_tac THEN
  c1092mocd_sector_tac 1 THEN c1092mocd_sector_tac 3 THEN
  c1092mocd_normal_tac `i:num` false THEN c1092mocd_normal_tac (c1092mocd_k 1) true THEN
  c1092mocd_normal_tac (c1092mocd_k 3) false THEN
  c1092mocd_point_tac 1 THEN c1092mocd_retains_tac [] THEN
  c1092mocd_apply C1092OPAC_MISSING_PREDECESSOR_POSITIVE_IMPOSSIBLE [c1092mocd_sq 3; c1092mocd_sq 1]);;

(* Lean: missing_before_retaining *)
let C1092MOCD_MISSING_BEFORE_RETAINING = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ ~(%s) /\\ ~%s /\\ ~(%s) /\\ %s /\\ ~(%s) /\\ %s /\\ %s ==> false"
    C1092AE_P C1092MOCD_CORE (c1092mocd_pos 3) (c1092mocd_ret 3) (c1092mocd_pos 0) (c1092mocd_ret 0)
    (c1092mocd_pos 1) (c1092mocd_ret 1) (c1092mocd_pos 2)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_base_tac THEN
  c1092mocd_sector_tac 1 THEN c1092mocd_sector_tac 3 THEN
  c1092mocd_normal_tac `i:num` false THEN c1092mocd_normal_tac (c1092mocd_k 1) false THEN
  c1092mocd_normal_tac (c1092mocd_k 3) false THEN
  c1092mocd_choose_p 2 THEN c1092mocd_point_tac 2 THEN c1092mocd_retains_tac [] THEN
  c1092mocd_apply C1092OPAC_MISSING_PREDECESSOR_RETAINING_IMPOSSIBLE [c1092mocd_sq 3; c1092mocd_sq 1]);;

(* Lean: positive_before_retaining *)
let C1092MOCD_POSITIVE_BEFORE_RETAINING = prove
 (parse_term (Printf.sprintf "forall %s cc cs cu cv ca i. %s /\\ %s /\\ ~(%s) /\\ %s /\\ ~(%s) /\\ %s /\\ %s ==> false"
    C1092AE_P C1092MOCD_CORE (c1092mocd_pos 3) (c1092mocd_pos 0) (c1092mocd_ret 0)
    (c1092mocd_pos 1) (c1092mocd_ret 1) (c1092mocd_pos 2)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mocd_base_tac THEN
  c1092mocd_sector_tac 1 THEN c1092mocd_sector_tac 3 THEN
  c1092mocd_normal_tac `i:num` false THEN c1092mocd_normal_tac (c1092mocd_k 1) false THEN
  c1092mocd_normal_tac (c1092mocd_k 3) true THEN
  c1092mocd_choose_p 2 THEN c1092mocd_point_tac 2 THEN c1092mocd_retains_tac [] THEN
  c1092mocd_apply C1092OPAC_POSITIVE_PREDECESSOR_RETAINING_IMPOSSIBLE [c1092mocd_sq 3; c1092mocd_sq 1]);;

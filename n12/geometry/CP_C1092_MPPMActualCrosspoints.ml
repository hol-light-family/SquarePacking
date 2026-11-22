(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualCrosspoints.lean               *)
(* (N12Compact.C1092MPPMActualCrosspoints; Lean header: "Source only,        *)
(* uncompiled").  Universal positive crosspoints in the actual ordinary      *)
(* four-cycle.  Conventions of CP_C1092_MPPMActualPositiveCycle.ml /         *)
(* MPPMActualRetaining.ml: owners p i at mask EL i c1092wc_code, side l;     *)
(* Ordinary p c1092mpapo_ordinary; ActualFrame p C c1092psa_frame (C's       *)
(* OpenSquare unit normal / positive side explicit); (rotation i).pullPacking*)
(* p is (d1,d2,e1,e2) with c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) *)
(* = (d1,d2,e1,e2) (other pulled packings use suffixed variables); addSector *)
(* c1092mar_addSector; Forward / Crosspoint c1092mapc_forward /              *)
(* c1092mapc_crosspoint; ScalarProof of the missing-negative transfer        *)
(* c1092mncac_scalarProof.  C : Fin 4 -> OpenSquare is cc cs cu cv ca :      *)
(* num->real used at i < 4 (unit normals / positive sides explicit).         *)
(* Used: rotated_frame C1092MAR_ROTATED_FRAME, forward_crosspoint            *)
(* C1092MAR_FORWARD_CROSSPOINT, positive_propagation_of_scalars /            *)
(* crosspoint_composed / next_crosspoint / backward_cycle C1092MAPC_*,       *)
(* MPPMActualPositiveCycle.scalar_proof / all_crosspoints C1092MAAP_*,       *)
(* MPPMNegativeCrosspointGeometry.crosspoint C1092NCC_CROSSPOINT,            *)
(* MPPMMissingNegativeCrosspointGeometry crosspoint_of_scalars / scalar_proof*)
(* C1092MNCAC_CROSSPOINT_OF_SCALARS / C1092MNCCO_SCALAR_PROOF.               *)
(* The private backward_cycle is C1092MAPC_BACKWARD_CYCLE.  Tag C1092MACR_.  *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualAllPositive.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeCrosspointComplete.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCrosspointComplete.ml";;

let C1092MACR_P = C1092AE_P;;

(* Lean: forward_composed_iff *)
let C1092MACR_FORWARD_COMPOSED_IFF =
  let own = map (fun f -> list_mk_comb(f, C1092MAPC_D0 @ [`l:real`; `EL 4 c1092wc_code`])) [`ooc`; `oos`; `oou`; `oov`] in
  let oc = el 0 own and os = el 1 own and ou = el 2 own and ov = el 3 own in
  let sq = [oc; os; mk_binop `(-):real->real->real` ou (mk_binop `(+):real->real->real`
                     (mk_binop `( * ):real->real->real` oc `&2`) (mk_binop `( * ):real->real->real` os `&2`));
            mk_binop `(-):real->real->real` ov (mk_binop `(+):real->real->real`
                     (mk_binop `( * ):real->real->real` (mk_comb(`(--):real->real`, os)) `&2`)
                     (mk_binop `( * ):real->real->real` oc `&2`)); `l:real`] in
  prove
   (parse_term (Printf.sprintf "!%s i j d10 d20 e10 e20 d1 d2 e1 e2 d12 d22 e12 e22.
        %s /\\ i < 4 /\\ j < 4 /\\ %s /\\ %s /\\ %s
        ==> (c1092mapc_forward d10 d20 e10 e20 l <=> c1092mapc_forward d12 d22 e12 e22 l)"
      C1092MACR_P C1092AE_HYP (c1092mapc_pks C1092MAPC_SUM C1092MAPC_V4 C1092MAPC_D0)
      (c1092mapc_pks `i:num` C1092MAPC_V4 C1092MAPC_D) (c1092mapc_pks `j:num` C1092MAPC_D C1092MAPC_D2)),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL (C1092MAPC_V @ [`i:num`; `j:num`] @ C1092MAPC_D0 @ C1092MAPC_D @ C1092MAPC_D2 @ sq)
      C1092MAR_ROTATED_FRAME) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c1092psa_frame; C1092PSA_INSIDE_TRANSLATED]; ALL_TAC] THEN
    REWRITE_TAC[c1092psa_frame; C1092PSA_INSIDE_TRANSLATED] THEN
    DISCH_THEN(MP_TAC o SPECL [`--(&13 / &50)`; `&0`]) THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REWRITE_TAC[c1092mapc_forward]);;

(* Lean: forward_composed *)
let C1092MACR_FORWARD_COMPOSED = prove
 (parse_term (Printf.sprintf "!%s i j d10 d20 e10 e20 d1 d2 e1 e2 d12 d22 e12 e22.
      %s /\\ i < 4 /\\ j < 4 /\\ %s /\\ %s /\\ %s /\\ c1092mapc_forward d10 d20 e10 e20 l
      ==> c1092mapc_forward d12 d22 e12 e22 l"
    C1092MACR_P C1092AE_HYP (c1092mapc_pks C1092MAPC_SUM C1092MAPC_V4 C1092MAPC_D0)
    (c1092mapc_pks `i:num` C1092MAPC_V4 C1092MAPC_D) (c1092mapc_pks `j:num` C1092MAPC_D C1092MAPC_D2)),
  MESON_TAC[C1092MACR_FORWARD_COMPOSED_IFF]);;

(* Lean: next_forward_iff *)
let C1092MACR_NEXT_FORWARD_IFF = prove
 (parse_term (Printf.sprintf "!%s d1 d2 e1 e2. %s /\\ %s ==> (c1092mapc_forward d1 d2 e1 e2 l <=> %s)"
    C1092MACR_P C1092AE_HYP C1092MAR_DPK1 (c1092mppe_in 5 "&2" "&87 / &50")),
  REPEAT GEN_TAC THEN REWRITE_TAC C1092MPAPO_ROT_ELS THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mapc_forward] THEN
  c1092mar_pull_tac C1092MAPC_V4 C1092MAPC_D `(true,true,false)` [4]);;

let C1092MACR_SUCC_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ c1092psa_frame d1 d2 e1 e2 l cD sD uD vD aD /\\ abs sD <= cD /\\ (&0 < sD ==> %s)"
  C1092MPAPO_HYPS C1092MAR_CHYPS C1092MAR_DPK1 C1092MAR_DSQ (c1092mppe_in 5 "&2" "&3 / &2");;

(* Lean: positive_crosspoint_of_successor *)
let C1092MACR_POSITIVE_CROSSPOINT_OF_SUCCESSOR = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD.
      c1092mncac_scalarProof /\\ %s ==> %s"
    C1092MACR_P C1092MACR_SUCC_HYPS (c1092mppe_in 4 "&3 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 4 "&87 / &50" "&2")) THENL
   [MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV) C1092MAR_FORWARD_CROSSPOINT) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 < sD` THENL
   [MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092MAPC_POSITIVE_PROPAGATION_OF_SCALARS) THEN
    ASM_SIMP_TAC[C1092MAAP_SCALAR_PROOF; c1092mapc_forward; c1092mapc_crosspoint] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`abs sD <= cD`; `&0 < sD`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cD (--sD)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
    MAP_EVERY UNDISCH_TAC [`abs sD <= cD`; `~(&0 < sD)`; `cD * cD + sD * sD = &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 5 "&2" "&87 / &50")) THENL
   [MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092NCC_CROSSPOINT);
    MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV @ C1092MAR_D @ C1092MAR_DV) C1092MNCAC_CROSSPOINT_OF_SCALARS)] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive_crosspoint *)
let C1092MACR_POSITIVE_CROSSPOINT =
  REWRITE_RULE[C1092MNCCO_SCALAR_PROOF] C1092MACR_POSITIVE_CROSSPOINT_OF_SUCCESSOR;;

(* the four frames C i *)
let C1092MACR_F4 = [`cc:num->real`; `cs:num->real`; `cu:num->real`; `cv:num->real`; `ca:num->real`];;
let C1092MACR_FRAMES =
  "(!i. i < 4 ==> cc i * cc i + cs i * cs i = &1 /\\ &0 < ca i) /\\
   (!i d1 d2 e1 e2. i < 4 /\\ c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2)
      ==> c1092psa_frame d1 d2 e1 e2 l (cc i) (cs i) (cu i) (cv i) (ca i)) /\\
   (!i. i < 4 ==> abs (cs i) <= cc i)";;
let C1092MACR_CONCL =
  "!i d1 d2 e1 e2. i < 4 /\\ c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2) /\\ &0 < cs i
      ==> c1092mapc_crosspoint d1 d2 e1 e2 l";;
let c1092macr_at k = map (fun f -> mk_comb(f, k)) C1092MACR_F4;;

(* instantiate the frame family at index k (k < 4 provable by ARITH / MOD_LT) *)
let c1092macr_inst_tac k =
  let side = ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092mar_addSector; MOD_LT_EQ; ARITH] in
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_forall c && can (find_term ((=) `ca:num->real`)) c && not (can (find_term ((=) `d1:num->real`)) c)
    then MP_TAC(SPEC k th) THEN ANTS_TAC THENL [side; STRIP_TAC] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_forall c && can (find_term ((=) `abs`)) c
    then MP_TAC(SPEC k th) THEN ANTS_TAC THENL [side; DISCH_TAC] else NO_TAC);;
let c1092macr_frame_tac k d4 =
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_forall c && can (find_term ((=) `c1092psa_frame`)) c
    then MP_TAC(SPECL (k :: d4) th) THEN
         ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092mar_addSector; MOD_LT_EQ; ARITH]; DISCH_TAC]
    else NO_TAC);;

(* Lean: positive_crosspoints_of_scalars *)
let C1092MACR_POSITIVE_CROSSPOINTS_OF_SCALARS = prove
 (parse_term (Printf.sprintf "!%s cc cs cu cv ca. c1092mncac_scalarProof /\\ %s /\\ %s ==> %s"
    C1092MACR_P C1092MPAPO_HYPS C1092MACR_FRAMES C1092MACR_CONCL),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `forall i. i < 4 ==> &0 < cs i` THENL
   [SUBGOAL_THEN (list_mk_comb(`c1092mapc_positiveFrames`, C1092MAPC_V)) ASSUME_TAC THENL
     [REWRITE_TAC[c1092mapc_positiveFrames] THEN
      MAP_EVERY X_GEN_TAC (`i:num` :: C1092MAPC_D) THEN STRIP_TAC THEN
      c1092macr_inst_tac `i:num` THEN c1092macr_frame_tac `i:num` C1092MAPC_D THEN
      MAP_EVERY EXISTS_TAC (c1092macr_at `i:num`) THEN ASM_SIMP_TAC[] THEN
      REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MAP_EVERY UNDISCH_TAC [`abs (cs (i:num)) <= cc i`] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(SPECL C1092MAPC_V C1092MAAP_ALL_CROSSPOINTS) THEN ASM_REWRITE_TAC[c1092mapc_allCrosspoints] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC (mk_abs(`i:num`, list_mk_forall(C1092MAPC_D,
      mk_imp(c1092mapc_pk `i:num` C1092MAPC_V4 C1092MAPC_D,
             `&0 < cs (i:num) ==> c1092mapc_crosspoint d1 d2 e1 e2 l`))))
    C1092MAPC_BACKWARD_CYCLE) THEN
  BETA_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ (c ==> d) ==> ((a /\ b ==> c) ==> d)`) THEN REPEAT CONJ_TAC THENL
   [(* the nonpositive seed *)
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    (* the backward step *)
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC C1092MAPC_D THEN REPEAT DISCH_TAC THEN
    c1092mapc_facts_tac C1092MAPC_V4 C1092MAPC_D `i:num` THEN
    c1092macr_inst_tac `i:num` THEN c1092macr_frame_tac `i:num` C1092MAPC_D THEN
    c1092macr_inst_tac `c1092mar_addSector i 1` THEN
    c1092mapc_choose_tac (c1092mapc_el `c1092mar_addSector i 1`) C1092MAPC_V4 C1092MAPC_D0 THEN
    c1092mapc_choose_tac (c1092mapc_el `1`) C1092MAPC_D C1092MAPC_D2 THEN
    c1092macr_frame_tac `c1092mar_addSector i 1` C1092MAPC_D0 THEN
    MP_TAC(SPECL (C1092MAPC_V @ [`i:num`; `1`] @ C1092MAPC_D0 @ C1092MAPC_D @ C1092MAPC_D2 @
                  c1092macr_at `c1092mar_addSector i 1`) C1092MAR_ROTATED_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
    REWRITE_TAC[c1092mapc_crosspoint] THEN
    MATCH_MP_TAC (SPECL (C1092MAPC_D5 @ c1092macr_at `i:num` @ C1092MAPC_D2 @ c1092macr_at `c1092mar_addSector i 1`)
      C1092MACR_POSITIVE_CROSSPOINT_OF_SUCCESSOR) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MAP_EVERY UNDISCH_TAC [`abs (cs (i:num)) <= cc i`] THEN REAL_ARITH_TAC;
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL C1092MAPC_D0 o
        check (fun th -> is_forall (concl th) && can (find_term ((=) `c1092mar_addSector i 1`)) (concl th) &&
                         can (find_term ((=) `c1092mapc_crosspoint`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(SPECL (C1092MAPC_V @ [`i:num`; `1`] @ C1092MAPC_D0 @ C1092MAPC_D @ C1092MAPC_D2)
        C1092MAPC_CROSSPOINT_COMPOSED) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
      MATCH_MP_TAC (SPECL (C1092MAPC_D5 @ C1092MAPC_D2) C1092MAPC_NEXT_CROSSPOINT) THEN
      ASM_REWRITE_TAC[]];
    (* conclusion *)
    MESON_TAC[]]);;

(* Lean: positive_crosspoints *)
let C1092MACR_POSITIVE_CROSSPOINTS =
  REWRITE_RULE[C1092MNCCO_SCALAR_PROOF] C1092MACR_POSITIVE_CROSSPOINTS_OF_SCALARS;;

(* Lean: nonpositive_retaining_crosspoint *)
let C1092MACR_NONPOSITIVE_RETAINING_CROSSPOINT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ %s ==> %s"
    C1092MACR_P C1092MPAPO_HYPS C1092MPOA_CHYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&3 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cC (--sC)`)) THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\ linside cC sC uC vC aC (--(&13 / &50)) (&0)`
    MP_TAC THENL [C1092MPAPO_FRAME_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[linside]) THEN
  SUBGOAL_THEN `linside cC sC uC vC aC (--(&1 / &2)) (&0)` MP_TAC THENL
   [REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C1092MPAPO_FRAME_TAC THEN REWRITE_TAC[]);;

(* Lean: retaining_crosspoint *)
let C1092MACR_RETAINING_CROSSPOINT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ abs sC <= cC /\\ %s ==> %s"
    C1092MACR_P C1092MPAPO_HYPS C1092MPOA_CHYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&3 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < sC` THENL
   [MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV) C1092MAR_FORWARD_CROSSPOINT);
    MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MAR_CV) C1092MACR_NONPOSITIVE_RETAINING_CROSSPOINT)] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
  MAP_EVERY UNDISCH_TAC [`abs sC <= cC`; `cC * cC + sC * sC = &1`] THEN
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC);;

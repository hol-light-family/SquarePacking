(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMAllNonpositiveActual.lean            *)
(* (N12Compact.C1092MPPMAllNonpositive; Lean header: "Source only,           *)
(* uncompiled").  Complete original-owner all-nonpositive ordinary ending.   *)
(* Conventions of CP_C1092_MPPMActualCrosspoints.ml / MPPMActualRetaining.ml *)
(* (owners p i at mask EL i c1092wc_code, side l; ActualFrame c1092psa_frame;*)
(* (rotation i).pullPacking p = (d1,d2,e1,e2) with c1092ot_pk (EL i         *)
(* c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2), other pulled packings   *)
(* with suffixed variables; Forward c1092mapc_forward; addSector             *)
(* c1092mar_addSector; C : Fin 4 -> OpenSquare is cc cs cu cv ca : num->real *)
(* used at i < 4).  clockwise D = (cD, sD, --vD - aD, uD, aD), counter-      *)
(* clockwise F = (cF, sF, vF, --uF - aF, aF); (owners pk 9).translated 2 2 = *)
(* c1092nopa_tr pk 9.  three_retaining_impossible / binary_cycle             *)
(* C1092MANCY_*; alternating_impossible C1092ANAL_ALTERNATING_IMPOSSIBLE;    *)
(* actual_core / bottom_bar C1092MANC_*; missing_strong_profile              *)
(* C1092MACOM_MISSING_STRONG_PROFILE; missing_predecessor / missing_successor*)
(* C1092MANP_*; adjacent_missing_impossible C1092MNCA_*; forward_composed(_iff)*)
(* / next_forward_iff C1092MACR_*.  Tag C1092ANPA_.                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMAllNonpositiveCycle.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_MPPMActualCrosspoints.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingNegativeCentersActual.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeOwnedPositiveActual.ml";;

let c1092anpa_d k = c1092mpapo_d4 k;;
let c1092anpa_d5 k = c1092mpapo_d4 k @ [`l:real`];;
let c1092anpa_sq k = map (fun n -> mk_var(n ^ k, `:real`)) ["c"; "s"; "u"; "v"; "a"];;
let c1092anpa_pk i base k =
  string_of_term (c1092mar_pk (mk_comb(mk_comb(`EL:num->(bool#bool#bool)list->bool#bool#bool`,
    mk_small_numeral i), `c1092mpapo_rotation`)) base (c1092anpa_d k));;
let c1092anpa_fr k sq =
  Printf.sprintf "c1092psa_frame %s %s" (String.concat " " (map (fun t -> fst(dest_var t)) (c1092anpa_d5 k)))
    (String.concat " " (map (fun t -> fst(dest_var t)) (c1092anpa_sq sq)));;
let c1092anpa_sqh sq = Printf.sprintf "c%s * c%s + s%s * s%s = &1 /\\ &0 < a%s" sq sq sq sq sq;;
let c1092anpa_fwd k = Printf.sprintf "c1092mapc_forward %s"
  (String.concat " " (map (fun t -> fst(dest_var t)) (c1092anpa_d5 k)));;

(* the frame equation of the frame of square sq in the packing whose first variable is v *)
let c1092anpa_freq v =
  ASSUM_LIST(fun ths -> let th = find (fun th -> c1092nopa_frame_of v th) ths in
    REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092psa_frame] th)]);;
let c1092anpa_seq v =
  ASSUM_LIST(fun ths -> let th = find (fun th -> c1092mpapo_head `c1092mar_successorFrame` th &&
      hd (snd (strip_comb (concl th))) = v) ths in
    REWRITE_TAC[CONJUNCT2 (REWRITE_RULE[c1092mar_successorFrame] th)]);;
(* ldisj of two squares whose insides were rewritten to owners i, j of packing pk *)
let c1092anpa_apart_tac pk i j =
  MP_TAC(SPECL (pk @ [mk_small_numeral i; mk_small_numeral j]) C1092WC_OWNERS_DISJOINT) THEN
  ASM_REWRITE_TAC[ldisj; ARITH] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]);;
let c1092anpa_side_tac v a =
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):real->real->bool`, `&1`), a)) ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of v)) THEN
    MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC];;
let c1092anpa_bar_tac pk sq =
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x. --(&14 / &25) <= x ==> x <= &0 ==> linside %s x (--(&1))"
      (c1092nopa_trs pk 9))) ASSUME_TAC THENL
   [REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC (SPECL (pk @ sq) C1092MANC_BOTTOM_BAR) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC];;

let C1092ANPA_THREE_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cD (--sD) /\\
      %s /\\ %s /\\ %s /\\ c977cc_normal cF (--sF) /\\ %s /\\ %s /\\ %s"
  C1092NFA_NHYPS C1092MAR_DPK1 (c1092anpa_sqh "D") (c1092anpa_fr "" "D")
  (c1092anpa_pk 2 C1092MPAPO_V4 "2") (c1092anpa_sqh "F") (c1092anpa_fr "2" "F")
  (c1092mppe_in 4 "&87 / &50" "&2") (c1092anpa_fwd "") (c1092anpa_fwd "2");;

(* Lean: actual_three_retaining_impossible *)
let C1092ANPA_ACTUAL_THREE_RETAINING_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD d12 d22 e12 e22 cF sF uF vF aF.
      %s ==> F" C1092AE_P C1092ANPA_THREE_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mapc_forward]) THEN
  (* the rotation-1 packing d and the rotation-2 packing d2 *)
  c1092mapc_facts_tac C1092MPAPO_V4 (c1092anpa_d "") `1` THEN
  c1092mapc_facts_tac C1092MPAPO_V4 (c1092anpa_d "2") `2` THEN
  (* F in the rotation-1 chart of d *)
  c1092mapc_choose_tac (c1092mapc_el `1`) (c1092anpa_d "") (c1092anpa_d "3") THEN
  MP_TAC(CONV_RULE(ONCE_DEPTH_CONV NUM_REDUCE_CONV) (REWRITE_RULE[c1092mar_addSector]
    (SPECL (C1092MAR_V @ [`1`; `1`] @ c1092anpa_d "2" @ c1092anpa_d "" @ c1092anpa_d "3" @
    c1092anpa_sq "F") C1092MAR_ROTATED_FRAME))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (c1092anpa_d5 "" @ c1092anpa_d "3" @ c1092anpa_sq "F") C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the three cores *)
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (c1092anpa_d5 "" @ C1092MAR_DV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (c1092anpa_d5 "2" @ c1092anpa_sq "F") C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the bars and their apartness *)
  c1092anpa_bar_tac C1092MAR_V C1092MAR_CV THEN
  c1092anpa_bar_tac (c1092anpa_d5 "") C1092MAR_DV THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj cC sC uC vC aC %s /\\ ldisj cD sD uD vD aD %s /\\
      ldisj cC sC uC vC aC cD sD (--vD - aD) uD aD /\\ ldisj cD sD uD vD aD cF sF (--vF - aF) uF aF"
      (c1092nopa_trs C1092MAR_V 9) (c1092nopa_trs (c1092anpa_d5 "") 9))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THENL
     [c1092anpa_freq `c1:num->real` THEN c1092anpa_apart_tac C1092MAR_V 4 9;
      c1092anpa_freq `d1:num->real` THEN c1092anpa_apart_tac (c1092anpa_d5 "") 4 9;
      c1092anpa_freq `c1:num->real` THEN c1092anpa_seq `c1:num->real` THEN c1092anpa_apart_tac C1092MAR_V 4 5;
      c1092anpa_freq `d1:num->real` THEN c1092anpa_seq `d1:num->real` THEN
      c1092anpa_apart_tac (c1092anpa_d5 "") 4 5];
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ C1092MAR_DV @ c1092anpa_sq "F" @ c1092nopa_tr C1092MAR_V 9 @
    c1092nopa_tr (c1092anpa_d5 "") 9) C1092MANCY_THREE_RETAINING_IMPOSSIBLE) THEN
  MP_TAC(SPECL (C1092MAR_V @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL (c1092anpa_d5 "" @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY RASM_ARITH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  REAL_ARITH_TAC);;

let C1092ANPA_ALT_HYPS = Printf.sprintf "%s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cD (--sD) /\\
      %s /\\ %s /\\ %s /\\ c977cc_normal cF (--sF) /\\ %s /\\ ~%s /\\ ~%s"
  C1092NFA_NHYPS C1092MAR_DPK1 (c1092anpa_sqh "D") (c1092anpa_fr "" "D")
  (c1092anpa_pk 3 C1092MPAPO_V4 "3") (c1092anpa_sqh "F") (c1092anpa_fr "3" "F")
  (c1092mppe_in 4 "&87 / &50" "&2") (c1092anpa_fwd "") (c1092anpa_fwd "3");;

(* Lean: actual_alternating_impossible *)
let C1092ANPA_ACTUAL_ALTERNATING_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC d1 d2 e1 e2 cD sD uD vD aD d13 d23 e13 e23 cF sF uF vF aF.
      %s ==> F" C1092AE_P C1092ANPA_ALT_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mapc_forward]) THEN
  c1092mapc_facts_tac C1092MPAPO_V4 (c1092anpa_d "") `1` THEN
  c1092mapc_facts_tac C1092MPAPO_V4 (c1092anpa_d "3") `3` THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_CV) C1092MANC_ACTUAL_CORE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (c1092anpa_d5 "" @ C1092MAR_DV) C1092MACOM_MISSING_STRONG_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (c1092anpa_d5 "3" @ c1092anpa_sq "F") C1092MACOM_MISSING_STRONG_PROFILE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  c1092anpa_side_tac `d1:num->real` `aD:real` THEN
  c1092anpa_side_tac `d13:num->real` `aF:real` THEN
  MP_TAC(SPECL C1092MAR_DV C1092MANP_MISSING_SUCCESSOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (c1092anpa_sq "F") C1092MANP_MISSING_PREDECESSOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MAR_D @ C1092MAR_DV) C1092MAR_SUCCESSOR_FRAME) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the counterclockwise turn W of F is the original owner 7 *)
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x y. linside cF sF vF (--uF - aF) aF x y <=> %s"
      (c1092mppe_in 7 "&2 + x" "&2 + y"))) ASSUME_TAC THENL
   [REWRITE_TAC[C1092MANP_INSIDE_COUNTERCLOCKWISE] THEN
    c1092anpa_freq `d13:num->real` THEN
    c1092mapc_lit_tac `3` C1092MPAPO_V4 (c1092anpa_d "3") THEN
    c1092mar_pull_tac C1092MPAPO_V4 (c1092anpa_d "3") `(true,false,true)` [4] THEN C1092MAR_POINT_EQ_TAC;
    ALL_TAC] THEN
  c1092anpa_bar_tac C1092MAR_V C1092MAR_CV THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "ldisj cC sC uC vC aC %s /\\
      ldisj cC sC uC vC aC cF sF vF (--uF - aF) aF /\\ ldisj cC sC uC vC aC cD sD (--vD - aD) uD aD"
      (c1092nopa_trs C1092MAR_V 9))) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REWRITE_TAC[ldisj; C1092PSA_INSIDE_TRANSLATED] THEN
    c1092anpa_freq `c1:num->real` THENL
     [c1092anpa_apart_tac C1092MAR_V 4 9;
      ASM_REWRITE_TAC[] THEN c1092anpa_apart_tac C1092MAR_V 4 7;
      c1092anpa_seq `c1:num->real` THEN c1092anpa_apart_tac C1092MAR_V 4 5];
    ALL_TAC] THEN
  MATCH_MP_TAC (SPECL (C1092MAR_CV @ [`cF:real`; `sF:real`; `vF:real`; `--uF - aF`; `aF:real`] @
    C1092MAR_E @ c1092nopa_tr C1092MAR_V 9) C1092ANAL_ALTERNATING_IMPOSSIBLE) THEN
  MP_TAC(SPECL (C1092MAR_V @ [`EL 9 c1092wc_code`]) OO_UNIT) THEN
  MP_TAC(SPECL C1092MAR_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY RASM_ARITH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `c1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d1:num->real`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092nopa_frame_of `d13:num->real`)) THEN
  TRY(ASM_REWRITE_TAC[] THEN NO_TAC) THEN
  c1092anpa_seq `c1:num->real` THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  C1092MPAPO_ORD_TAC THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  REWRITE_TAC[c1092psa_seed 7 (`&33 / &20`, `&47 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`)] THEN
  ASM_REWRITE_TAC[]);;

(* the retains predicate of a rotation, read off at the chosen pulled packing *)
let C1092ANPA_R_AT = prove
 (`forall q d1 d2 e1 e2 (l:real). q = (d1,d2,e1,e2)
     ==> ((forall x1 x2 x3 x4. q = (x1,x2,x3,x4) ==> c1092mapc_forward x1 x2 x3 x4 l) <=>
          c1092mapc_forward d1 d2 e1 e2 l)`,
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[PAIR_EQ] THEN MESON_TAC[]);;

let C1092ANPA_F4 = [`cc:num->real`; `cs:num->real`; `cu:num->real`; `cv:num->real`; `ca:num->real`];;
let c1092anpa_at k = map (fun f -> mk_comb(f, k)) C1092ANPA_F4;;
let C1092ANPA_FRAMES =
  "(!i. i < 4 ==> cc i * cc i + cs i * cs i = &1 /\\ &0 < ca i) /\\
   (!i d1 d2 e1 e2. i < 4 /\\ c1092ot_pk (EL i c1092mpapo_rotation) (c1,c2,a,b) = (d1,d2,e1,e2)
      ==> c1092psa_frame d1 d2 e1 e2 l (cc i) (cs i) (cu i) (cv i) (ca i)) /\\
   (!i. i < 4 ==> c977cc_normal (cc i) (--(cs i)))";;

let c1092anpa_side = ASM_REWRITE_TAC[] THEN REWRITE_TAC[c1092mar_addSector; MOD_LT_EQ; ARITH];;
let c1092anpa_inst_tac k =
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_forall c && can (find_term ((=) `ca:num->real`)) c && not (can (find_term ((=) `d1:num->real`)) c)
    then MP_TAC(SPEC k th) THEN ANTS_TAC THENL [c1092anpa_side; STRIP_TAC] else NO_TAC) THEN
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_forall c && can (find_term ((=) `c977cc_normal`)) c
    then MP_TAC(SPEC k th) THEN ANTS_TAC THENL [c1092anpa_side; DISCH_TAC] else NO_TAC);;
let c1092anpa_frame_tac k d4 =
  FIRST_ASSUM(fun th -> let c = concl th in
    if is_forall c && can (find_term ((=) `c1092psa_frame`)) c
    then MP_TAC(SPECL (k :: d4) th) THEN ANTS_TAC THENL [c1092anpa_side; DISCH_TAC]
    else NO_TAC);;
(* read retains at packing d4 = pk (EL k) base *)
let c1092anpa_read_tac k d4 =
  let pk = c1092mar_pk (c1092mapc_el k) C1092MPAPO_V4 d4 in
  RULE_ASSUM_TAC(REWRITE_RULE[MATCH_MP C1092ANPA_R_AT (ASSUME pk)]);;
(* the square C (addSector i k) in the rotation-k chart drot of D, and the forward transfer *)
let c1092anpa_step_tac k dorig drot =
  let ks = mk_small_numeral k in
  let ik = mk_comb(mk_comb(`c1092mar_addSector`, `i:num`), ks) in
  c1092anpa_inst_tac ik THEN
  c1092mapc_choose_tac (c1092mapc_el ik) C1092MPAPO_V4 dorig THEN
  c1092mapc_choose_tac (c1092mapc_el ks) C1092MAR_D drot THEN
  c1092anpa_frame_tac ik dorig THEN
  MP_TAC(SPECL (C1092MAR_V @ [`i:num`; ks] @ dorig @ C1092MAR_D @ drot @ c1092anpa_at ik) C1092MAR_ROTATED_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
  MP_TAC(SPECL (C1092MAR_V @ [`i:num`; ks] @ dorig @ C1092MAR_D @ drot) C1092MACR_FORWARD_COMPOSED_IFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REWRITE_TAC[ARITH]; DISCH_TAC] THEN
  c1092anpa_read_tac ik dorig;;

let C1092ANPA_BASE_TAC =
  X_GEN_TAC `i:num` THEN REPEAT DISCH_TAC THEN
  c1092mapc_choose_tac (c1092mapc_el `i:num`) C1092MPAPO_V4 C1092MAR_D THEN
  c1092mapc_facts_tac C1092MPAPO_V4 C1092MAR_D `i:num` THEN
  c1092anpa_inst_tac `i:num` THEN c1092anpa_frame_tac `i:num` C1092MAR_D THEN
  c1092anpa_read_tac `i:num` C1092MAR_D;;

(* Lean: impossible *)
let C1092ANPA_IMPOSSIBLE = prove
 (parse_term (Printf.sprintf "!%s cc cs cu cv ca. %s /\\ %s ==> F" C1092AE_P C1092MPAPO_HYPS C1092ANPA_FRAMES),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC (mk_abs(`i:num`, list_mk_forall([`x1:num->real`; `x2:num->real`; `x3:num->real`; `x4:num->real`],
      mk_imp(c1092mar_pk (c1092mapc_el `i:num`) C1092MPAPO_V4
               [`x1:num->real`; `x2:num->real`; `x3:num->real`; `x4:num->real`],
             `c1092mapc_forward x1 x2 x3 x4 l`)))) C1092MANCY_BINARY_CYCLE) THEN
  BETA_TAC THEN PURE_REWRITE_TAC[GSYM c1092mar_addSector] THEN
  MATCH_MP_TAC(TAUT `a /\ b /\ c ==> (a /\ b /\ c ==> false) ==> false`) THEN REPEAT CONJ_TAC THENL
   [(* two adjacent missing *)
    C1092ANPA_BASE_TAC THEN c1092anpa_step_tac 1 (c1092anpa_d "0") (c1092anpa_d "2") THEN
    MP_TAC(SPECL (C1092MANH_D5 @ c1092anpa_d "2") C1092MACR_NEXT_FORWARD_IFF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC (SPECL (C1092MANH_D5 @ c1092anpa_at `i:num` @ c1092anpa_d "2" @
      c1092anpa_at `c1092mar_addSector i 1`) C1092MNCA_ADJACENT_MISSING_IMPOSSIBLE) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092mapc_forward]) THEN ASM_MESON_TAC[];
    (* three retaining *)
    C1092ANPA_BASE_TAC THEN c1092anpa_step_tac 1 (c1092anpa_d "0") (c1092anpa_d "2") THEN
    c1092anpa_step_tac 2 (c1092anpa_d "5") (c1092anpa_d "4") THEN
    MATCH_MP_TAC (SPECL (C1092MANH_D5 @ c1092anpa_at `i:num` @ c1092anpa_d "2" @
      c1092anpa_at `c1092mar_addSector i 1` @ c1092anpa_d "4" @ c1092anpa_at `c1092mar_addSector i 2`)
      C1092ANPA_ACTUAL_THREE_RETAINING_IMPOSSIBLE) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092mapc_forward]) THEN REWRITE_TAC[c1092mapc_forward] THEN
    ASM_MESON_TAC[];
    (* alternating *)
    C1092ANPA_BASE_TAC THEN c1092anpa_step_tac 1 (c1092anpa_d "0") (c1092anpa_d "2") THEN
    c1092anpa_step_tac 3 (c1092anpa_d "7") (c1092anpa_d "6") THEN
    MATCH_MP_TAC (SPECL (C1092MANH_D5 @ c1092anpa_at `i:num` @ c1092anpa_d "2" @
      c1092anpa_at `c1092mar_addSector i 1` @ c1092anpa_d "6" @ c1092anpa_at `c1092mar_addSector i 3`)
      C1092ANPA_ACTUAL_ALTERNATING_IMPOSSIBLE) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092mapc_forward]) THEN REWRITE_TAC[c1092mapc_forward] THEN
    ASM_MESON_TAC[]]);;

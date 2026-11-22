(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualInwardSuccessor.lean           *)
(* (N12Compact.C1092MPPMActualInward).  The actual negative inward owner     *)
(* produces its successor's sign and full bar profile, then the centered cap *)
(* and angle input.  (Lean header: "Source only, uncompiled".)               *)
(* Conventions of CP_C1092_MPPMActualInwardPoints.ml / MPPMActualInwardMissing.ml: *)
(* owners p i at mask EL i c1092wc_code (side l); Frame p i C is             *)
(* c1092mpai_frame c1 c2 a b l i cC sC uC vC aC (squares C, E, W; their      *)
(* OpenSquare unit normal / positive side explicit where the used lemmas     *)
(* need them); Inward / Ordinary c1092mcc_inward / c1092mcc_ordinary;        *)
(* Normal c977cc_normal; half C1092WPS_half.  SignInput c1092mifs_signInput, *)
(* successor_negative C1092MIFS_SUCCESSOR_NEGATIVE; NegativeSuccessor        *)
(* c1092ifsu_negsucc, negative_successor C1092IFBP_NEGATIVE_SUCCESSOR;       *)
(* centered_marker_caps / centered_lower_face / centered_first_cap           *)
(* C1092IFCC_*; CenteredCapInput c1092ifh_capInput, centered_height_cap      *)
(* C1092IFH_CENTERED_HEIGHT_CAP; centered_half_angle /                       *)
(* centered_outer_consequences C1092IFA_*; normal_bounds C977CC_NORMAL_BOUNDS;*)
(* owners_disjoint / marker_owned / corner_points via oo_apart / oo_seed     *)
(* (c1092moc_excl, c1092moc_seed); canonical_frame C1092MPAI_CANONICAL_FRAME.*)
(* Tag C1092MPAIS_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualInwardMissing.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSign.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalAngle.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalHeight.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBarProfile.ml";;

let c1092mpais_sq n = map (fun f -> mk_var(f ^ n, `:real`)) ["c"; "s"; "u"; "v"; "a"];;
let C1092MPAIS_C = c1092mpais_sq "C" and C1092MPAIS_E = c1092mpais_sq "E"
and C1092MPAIS_W = c1092mpais_sq "W";;
let c1092mpais_frame i n = Printf.sprintf "c1092mpai_frame c1 c2 a b l %d c%s s%s u%s v%s a%s" i n n n n n;;
let c1092mpais_unit n = Printf.sprintf "c%s * c%s + s%s * s%s = &1 /\\ &0 < a%s" n n n n n;;
let c1092mpais_in = c1092mppe_in;;
let c1092mpais_lit i x y = list_mk_comb(`linside`, c1092moc_own i @ [x; y]);;

let c1092mpais_frame_of n th =
  let t = concl th in
  is_comb t && fst (strip_comb t) = `c1092mpai_frame` && can (find_term ((=) (mk_var("c" ^ n, `:real`)))) t;;
(* rewrite square n's insides into the owner's (reduced coordinates) *)
let C1092MPAIS_FRAME_CONV_TAC n =
  FIRST_ASSUM(fun th -> if c1092mpais_frame_of n th
    then CONV_TAC(REWRITE_CONV[CONJUNCT2 (REWRITE_RULE[c1092mpai_frame] th)] THENC
                  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) else NO_TAC);;
(* a fact of square n proved from owner facts (literal masks) *)
let c1092mpais_fact n tm ths =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [C1092MPAIS_FRAME_CONV_TAC n THEN CONV_TAC C1092MOC_CODE_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE C1092MOC_CODE_CONV) THEN ASM_REWRITE_TAC ths;
    ALL_TAC];;
(* side facts: a_n = l for every frame, &1 < l; closes a real goal *)
let C1092MPAIS_SIDES_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092mpai_frame])
                          (filter c1092mpaim_is_frame ths)) THEN
  MP_TAC(c1092moc_side ()) THEN REAL_ARITH_TAC;;
let c1092mpais_lin_tac =
  REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; C1092MPAIS_SIDES_TAC; RASM_ARITH_TAC];;
let c1092mpais_apart_tac i n j m =
  MP_TAC(SPECL (C1092MPPE_V @ [mk_small_numeral i; mk_small_numeral j] @ c1092mpais_sq n @ c1092mpais_sq m)
    C1092MPAI_FRAME_APART) THEN ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC;;
let c1092mpais_cin n x y = list_mk_comb(`linside`, c1092mpais_sq n @ [x; y]);;

(* Lean: central_anchors *)
let C1092MPAIS_CENTRAL_ANCHORS = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s ==> %s"
    C1092AE_P C1092AE_HYP (c1092mpais_frame 4 "C")
    (string_of_term (list_mk_conj [c1092mpais_cin "C" `--(&7 / &20)` `--(&7 / &20)`;
       mk_neg (c1092mpais_cin "C" `&7 / &20` `--(&7 / &20)`);
       mk_neg (c1092mpais_cin "C" `--(&7 / &20)` `&7 / &20`)]))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MPAIS_FRAME_CONV_TAC "C" THEN CONV_TAC C1092MOC_CODE_CONV THEN
  REWRITE_TAC[c1092moc_seed 4 (`&33 / &20`, `&33 / &20`);
    c1092moc_excl 4 5 (c1092moc_seed 5 (`&47 / &20`, `&33 / &20`));
    c1092moc_excl 4 7 (c1092moc_seed 7 (`&33 / &20`, `&47 / &20`))]);;

let C1092MPAIS_NEG_HYPS = Printf.sprintf "%s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ %s"
  C1092AE_HYP C1092MCC_OWN4 C1092MCC_OWN4 (c1092mpais_frame 4 "C") (c1092mpais_unit "C");;

(* Lean: negative_faces *)
let C1092MPAIS_NEGATIVE_FACES = prove
 (parse_term (Printf.sprintf
   "!%s cC sC uC vC aC. %s ==> --cC - (&13 / &50) * sC <= uC /\\ vC + aC <= (&7 / &20) * (cC + sC)"
    C1092AE_P C1092MPAIS_NEG_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mcc_ordinary; c1092mcc_inward]) THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `&0` `--(&13 / &50)`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&13 / &50)` `&0`) [] THEN
  c1092mpais_fact "C" (mk_neg (mk_conj(c1092mpais_cin "C" `--(&1)` `--(&13 / &50)`,
                                       c1092mpais_cin "C" `--(&1)` `--(&2 / &5)`))) [] THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C977CC_NORMAL_BOUNDS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `vC + aC <= (&7 / &20) * (cC + sC)` ASSUME_TAC THENL
   [ASM_CASES_TAC (c1092mpais_cin "C" `&0` `&0`) THENL
     [MP_TAC(SPECL C1092MPAIS_C C1092IFCC_CENTERED_MARKER_CAPS) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[];
      SUBGOAL_THEN `vC + aC <= &0` MP_TAC THENL
       [REFUTE_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NOT_LE]) THEN
        MAP_EVERY (fun t -> UNDISCH_TAC t)
          [c1092mpais_cin "C" `--(&13 / &50)` `&0`; c1092mpais_cin "C" `&0` `--(&13 / &50)`;
           c1092mpais_cin "C" `--(&7 / &20)` `--(&7 / &20)`; mk_neg (c1092mpais_cin "C" `&0` `&0`)] THEN
        MAP_EVERY UNDISCH_TAC [`&0 < vC + aC`; `&7 / &10 <= cC`; `c977cc_normal cC (--sC)`] THEN
        REWRITE_TAC[linside; c977cc_normal] THEN REAL_ARITH_TAC;
        UNDISCH_TAC `c977cc_normal cC (--sC)` THEN REWRITE_TAC[c977cc_normal] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL C1092MPAIS_C C1092IFCC_CENTERED_LOWER_FACE) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let C1092MPAIS_INPUT_HYPS = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ %s"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4 (c1092mpais_frame 4 "C") (c1092mpais_frame 5 "E")
  (c1092mpais_unit "C");;

(* Lean: successor_input *)
let C1092MPAIS_SUCCESSOR_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cE sE uE vE aE. %s ==> c1092mifs_signInput cC sC uC vC aC cE sE uE vE aE"
    C1092AE_P C1092MPAIS_INPUT_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092MPAI_NO_MISSING_TAC THEN
  c1092mpai_use C1092MIN_SOUTHWEST_CROSSPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MIN_SOUTHEAST_PAIR THEN STRIP_TAC THEN
  c1092mpai_use C1092MPAI_SUCCESSOR_HALFPOINT THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_NEGATIVE_FACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN
  C1092MPAI_INWARD_TAC THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `&0` `--(&13 / &50)`) [] THEN
  c1092mpais_fact "C" (c1092mpais_cin "C" `--(&1 / &2)` `&0`) [] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&7 / &20` `--(&7 / &20)`) [c1092moc_seed 5 (`&47 / &20`, `&33 / &20`)] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&13 / &50` `--(&1)`) [] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&2 / &5` `--(&1)`) [] THEN
  c1092mpais_fact "E" (c1092mpais_cin "E" `&1 / &2` `--(&1)`) [] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&0` `--(&13 / &50)`))
    [c1092moc_excl 5 4 (ASSUME (c1092mpais_lit 4 `&2` `&87 / &50`))] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&2 / &5)`))
    [c1092moc_excl 5 10 (ASSUME (c1092mpais_lit 10 `&3` `&8 / &5`))] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&0` `--(&543 / &500)`))
    [c1092moc_excl 5 9 (c1092moc_seed 9 (`&2`, `&457 / &500`))] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&1)`))
    [c1092moc_excl 5 1 (c1092moc_seed 1 (`&3`, `&1`))] THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `--(&543 / &500)`))
    [c1092moc_excl 5 1 (c1092moc_seed 1 (`&3`, `&457 / &500`))] THEN
  REWRITE_TAC[c1092mifs_signInput] THEN ASM_REWRITE_TAC[] THEN c1092mpais_lin_tac);;

let C1092MPAIS_PROFILE_HYPS = Printf.sprintf "%s /\\ %s /\\ abs sE <= cE" C1092MPAIS_INPUT_HYPS (c1092mpais_unit "E");;

(* Lean: successor_profile *)
let C1092MPAIS_SUCCESSOR_PROFILE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cE sE uE vE aE. %s ==> sE < &0 /\\ c1092ifsu_negsucc cE sE uE vE aE"
    C1092AE_P C1092MPAIS_PROFILE_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIS_SUCCESSOR_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPAIS_C @ C1092MPAIS_E) C1092MIFS_SUCCESSOR_NEGATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[] THEN
  c1092mpai_use C1092MPAI_RIGHT_ORIGIN THEN DISCH_TAC THEN
  c1092mpai_use C1092MPAI_RIGHT_BAR THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ [`5`; `10`] @ C1092MPAIS_E @ c1092mpai_chart "10") C1092MPAI_FRAME_APART) THEN
  ASM_REWRITE_TAC[SPECL (C1092MPPE_V @ [`10`]) C1092MPAI_CHART_FRAME; ARITH] THEN DISCH_TAC THEN
  c1092mpais_fact "E" (mk_neg (c1092mpais_cin "E" `&1` `&0`))
    [c1092moc_excl 5 10 (CONV_RULE C1092MOC_CODE_CONV (ASSUME (parse_term (c1092mpais_in 10 "&3" "&2"))))] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mifs_signInput] o
    check (fun th -> can (term_match [] `c1092mifs_signInput a b c d e f g h i j`) (concl th))) THEN
  MATCH_MP_TAC (SPECL (C1092MPAIS_E @ c1092mpai_chart "10") C1092IFBP_NEGATIVE_SUCCESSOR) THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN
  REPEAT CONJ_TAC THEN FIRST
   [FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[IMP_CONJ] THEN FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[REAL_POW_2; REAL_NEG_MUL2] THEN FIRST_ASSUM ACCEPT_TAC;
    RASM_ARITH_TAC]);;

let C1092MPAIS_CENTERED_HYPS = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ %s /\\ %s /\\ %s /\\ abs sE <= cE"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4 (c1092mpais_in 4 "&2" "&2")
  (c1092mpais_frame 4 "C") (c1092mpais_frame 5 "E") (c1092mpais_frame 7 "W")
  (c1092mpais_unit "C") (c1092mpais_unit "E") (c1092mpais_unit "W");;

(* Lean: centered_input *)
let C1092MPAIS_CENTERED_INPUT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cE sE uE vE aE cW sW uW vW aW. %s ==> c1092ifh_capInput cC sC uC vC aC cW sW uW vW aW"
    C1092AE_P C1092MPAIS_CENTERED_HYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C) C1092MPAIS_CENTRAL_ANCHORS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E) C1092MPAIS_SUCCESSOR_PROFILE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_W) C1092MPAI_PREDECESSOR_POINTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpais_apart_tac 4 "C" 5 "E" THEN c1092mpais_apart_tac 4 "C" 7 "W" THEN
  SUBGOAL_THEN (c1092mpais_cin "C" `&0` `&0`) ASSUME_TAC THENL
   [C1092MPAIS_FRAME_CONV_TAC "C" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL [C1092MPAIS_SIDES_TAC; ALL_TAC] THEN
  MP_TAC(SPECL C1092MPAIS_C C1092IFCC_CENTERED_MARKER_CAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPAIS_C @ C1092MPAIS_E) C1092IFCC_CENTERED_FIRST_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MPAIS_SIDES_TAC; DISCH_TAC] THEN
  REWRITE_TAC[c1092ifh_capInput] THEN ASM_REWRITE_TAC[] THEN C1092MPAIS_SIDES_TAC);;

let C1092MPAIS_NEGATIVE_HYPS = Printf.sprintf "%s /\\ %s /\\ c1092mcc_inward %s /\\ ~c1092mcc_ordinary %s /\\ %s /\\ %s /\\ c977cc_normal cC (--sC) /\\ sC < &0 /\\ %s"
  C1092AE_HYP C1092MPPE_CTX C1092MCC_OWN4 C1092MCC_OWN4 (c1092mpais_in 4 "&2" "&2")
  (c1092mpais_frame 4 "C") (c1092mpais_unit "C");;

(* Lean: centered_negative *)
let C1092MPAIS_CENTERED_NEGATIVE = prove
 (parse_term (Printf.sprintf
   "!%s cC sC uC vC aC. %s ==> uC + aC <= (&7 / &50) * cC - sC / &2 /\\ vC + aC < &17 / &125 /\\ C1092WPS_half cC (--sC) < &21 / &100 /\\ ~%s /\\ (%s ==> %s /\\ %s)"
    C1092AE_P C1092MPAIS_NEGATIVE_HYPS (c1092mpais_in 4 "&1" "&87 / &50") (c1092mpais_in 4 "&1" "&8 / &5")
    (c1092mpais_in 4 "&1" "&3 / &2") (c1092mpais_in 9 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (i, n) ->
    MP_TAC(SPECL (C1092MPPE_V @ [mk_small_numeral i]) C1092MPAI_CANONICAL_FRAME) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC (c1092mpais_sq n) THEN STRIP_TAC) [5, "E"; 7, "W"] THEN
  MP_TAC(SPECL (C1092MPPE_V @ C1092MPAIS_C @ C1092MPAIS_E @ C1092MPAIS_W) C1092MPAIS_CENTERED_INPUT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (mk_conj(c1092mpais_cin "C" `--(&1)` `--(&13 / &50)`,
                                c1092mpais_cin "C" `--(&1)` `--(&2 / &5)`))) ASSUME_TAC THENL
   [C1092MPAIS_FRAME_CONV_TAC "C" THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) &&
      can (find_term ((=) `c1092mcc_ordinary`)) (concl th))) THEN
    REWRITE_TAC[c1092mcc_ordinary];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MPAIS_C @ C1092MPAIS_W) C1092IFA_CENTERED_OUTER_CONSEQUENCES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MPAIS_C @ C1092MPAIS_W) C1092IFH_CENTERED_HEIGHT_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092MPAIS_C @ C1092MPAIS_W) C1092IFA_CENTERED_HALF_ANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o el 7 o CONJUNCTS o REWRITE_RULE[c1092ifh_capInput] o
    check (fun th -> can (term_match [] `c1092ifh_capInput a b c d e f g h i j`) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = mk_neg (c1092mpais_cin "C" `--(&1)` `--(&13 / &50)`))) THEN
    C1092MPAIS_FRAME_CONV_TAC "C" THEN REWRITE_TAC[];
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp (concl th) &&
      concl th = mk_imp(c1092mpais_cin "C" `--(&1)` `--(&2 / &5)`, c1092mpais_cin "C" `--(&1)` `--(&1 / &2)`))) THEN
    C1092MPAIS_FRAME_CONV_TAC "C" THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    c1092mpai_use C1092MPAWR_WALL_PAIRS THEN STRIP_TAC THEN
    MP_TAC(SPECL C1092MPPE_V C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT) THEN ASM_REWRITE_TAC[]]);;

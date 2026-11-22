(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeForwardActual.lean           *)
(* (N12Compact.C1092MPPMNegativeForwardActual; Lean header: "Source only,    *)
(* uncompiled").  Literal Corollary 3 of NEGATIVE-FORWARD-POSITIVE-H.        *)
(* Conventions of CP_C1092_MPPMActualCentralOrigin.ml: ActualFrame p C is    *)
(* c1092psa_frame, OwnerFrame p 5 J is c1092fpda_frame .. 5 J (OpenSquare    *)
(* invariants as hypotheses); J.translated 2 2 and (owners p 9).translated  *)
(* 2 2 are the tuples of C1092PSA_INSIDE_TRANSLATED; rotation 1 via          *)
(* c1092mpapo_rot_tac / c1092mpapo_pull_tac.  NegativeForward Input / point: *)
(* c1092nff_input / C1092NFW_POINT; inside_segment OO_HORIZONTAL_SEGMENT.    *)
(* The private side_gt / side_same / mark are OO_SIDE / l = l / oo_seed.     *)
(* Tag C1092NFA_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMNegativeForward.ml";;
needs "n12/geometry/CP_C1092_MPPMActualCentralOrigin.ml";;

(* Lean: side_gt (private) *)
let C1092NFA_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092NFA_SIDE_SAME = C1092MPAPO_SIDE_SAME;;
(* Lean: mark (private) *)
let C1092NFA_MARK = C1092MPAPO_MARK;;

let C1092NFA_NHYPS = Printf.sprintf "%s /\\ %s /\\ c977cc_normal cC (--sC)" C1092MPAPO_HYPS C1092MPOA_CHYPS;;
let C1092NFA_FORWARD = c1092mppe_in 4 "&87 / &50" "&2";;

(* Lean: bottom_segment *)
let C1092NFA_BOTTOM_SEGMENT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC x. %s /\\ &36 / &25 <= x /\\ x <= &2 ==> %s"
    C1092AE_P C1092NFA_NHYPS (c1092mppe_in 9 "x" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mabo_normal_tac `cC:real` `--sC` THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MPOA_CT) C1092MANH_BOTTOM_ORIGIN) THEN
  ASM_SIMP_TAC[C1092MPOA_OWNER_FRAME] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&36 / &25`; `&2`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let C1092NFA_JV = [`cJ:real`; `sJ:real`; `uJ:real`; `vJ:real`; `aJ:real`];;
let C1092NFA_E = [`cJ:real`; `sJ:real`; `uJ - (cJ * &2 + sJ * &2)`; `vJ - (--sJ * &2 + cJ * &2)`; `aJ:real`];;

(* Lean: positive_retaining_successor (private) *)
let C1092NFA_POSITIVE_RETAINING_SUCCESSOR = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cJ sJ uJ vJ aJ. %s /\\ %s /\\ %s /\\ %s /\\ c977cc_normal cJ sJ /\\ %s
      ==> %s"
    C1092AE_P C1092NFA_NHYPS C1092NFA_FORWARD C1092MANH_SQJ C1092MANH_FRJ (c1092mppe_in 5 "&2" "&87 / &50")
    (c1092mppe_in 5 "&5 / &2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MACO_CV) C1092MACO_NONPOSITIVE_RETAINING_EXCLUDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MPAPO_ORD_TAC THEN C1092MABO_SIDE_TAC THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "!x. --(&14 / &25) <= x /\\ x <= &0 ==> %s" (c1092mppe_in 9 "&2 + x" "&1")))
    ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MACO_CV @ [`&2 + x`]) C1092NFA_BOTTOM_SEGMENT) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o
    check (fun th -> c1092mpapo_head `c1092psa_frame` th)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092fpda_frame] o
    check (fun th -> c1092mpapo_head `c1092fpda_frame` th)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aJ:real = l`))) THEN
  MP_TAC(SPECL ([`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`] @
                [`cJ:real`; `sJ:real`; `uJ - (cJ * &2 + sJ * &2)`; `vJ - (--sJ * &2 + cJ * &2)`; `l:real`] @
                c1092mabo_tr 9) C1092NFW_POINT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[c1092nff_input; ldisj; C1092PSA_INSIDE_TRANSLATED] THEN ASM_REWRITE_TAC[c1092psa_unit 9; c1092psa_pos ()] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    REWRITE_TAC[c1092psa_seed 4 (`&33 / &20`, `&33 / &20`); c1092psa_seed 5 (`&47 / &20`, `&33 / &20`);
                c1092psa_excl 4 7 (c1092psa_seed 7 (`&33 / &20`, `&47 / &20`));
                c1092psa_apart 4 5; c1092psa_apart 4 9] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[C1092PSA_INSIDE_TRANSLATED] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  REWRITE_TAC[]);;

(* Lean: successor_halfpoint *)
let C1092NFA_SUCCESSOR_HALFPOINT = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s ==> %s"
    C1092AE_P C1092NFA_NHYPS C1092NFA_FORWARD (c1092mppe_in 5 "&5 / &2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ [`5`]) C1092FPDA_EXISTS_OWNER_FRAME) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) C1092NFA_JV THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < sJ` THENL
   [ASM_CASES_TAC (parse_term (c1092mppe_in 5 "&2" "&87 / &50")) THENL
     [MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092MACO_CV @ C1092NFA_JV) C1092NFA_POSITIVE_RETAINING_SUCCESSOR) THEN
      ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC (SPECL C1092MAR_V C1092MANH_SOUTHEAST_OF_MISSING) THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC (SPECL (C1092MAR_V @ C1092NFA_JV) C1092MANH_SOUTHEAST) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: right_origin *)
let C1092NFA_RIGHT_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s ==> %s"
    C1092AE_P C1092NFA_NHYPS C1092NFA_FORWARD (c1092mppe_in 10 "&3" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MAR_V @ C1092MACO_CV) C1092NFA_SUCCESSOR_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092manh_rot_tac 1 THEN
  MP_TAC(SPECL C1092MANH_D5 C1092MPAWR_BOTTOM_ORDINARY) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MANH_D5 C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN
  c1092mpapo_pull_tac (c1092mpapo_d4 "") `(true,true,false)` [4; 9] THEN ASM_REWRITE_TAC[]);;

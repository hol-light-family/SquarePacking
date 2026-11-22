(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMForwardPositiveDActual.lean          *)
(* (N12Compact.C1092MPPMForwardPositiveD; Lean header: "Source-only; no      *)
(* compiler acceptance is claimed").  Actual-owner part of FORWARD-OWNED-    *)
(* POSITIVE-D Theorem 1.  Conventions of CP_C1092_MPPMEntrance.ml /          *)
(* CP_C1092_MPPMPositiveSeedsActual.ml (forward toolkit c1092psa_* at        *)
(* literal masks): owners p i is the owner 5-tuple at mask EL i c1092wc_code *)
(* (side l); WallContext p mppm is c1092wc_ctx c1 c2 a b l c1092mppe_mppm;   *)
(* Missing is c1092mom_missing.  An OpenSquare C is cC sC uC vC aC with its  *)
(* invariants as hypotheses; OwnerFrame p i C is c1092fpda_frame .. i C;     *)
(* Predecessor is c1092fpdf_predecessor; previous_origin_excluded is         *)
(* C1092FPDL_PREVIOUS_ORIGIN_EXCLUDED; WallProfile.boundary_origin is        *)
(* OCWPBO_BOUNDARY_ORIGIN; bottom_origin_of_missing / _of_halfpoint are      *)
(* C1092PSA_BOTTOM_ORIGIN_OF_MISSING / _OF_HALFPOINT.  Tag C1092FPDA_.       *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMForwardPositiveDLocal.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveSeedsActual.ml";;
needs "n12/geometry/CP_C1092_MPPMOmissions.ml";;

(* Lean: OwnerFrame (structure) *)
let c1092fpda_frame = new_definition
 `c1092fpda_frame (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) (i:num)
                  (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) <=>
    aC = l /\
    forall x y. linside cC sC uC vC aC x y <=>
          linside (ooc c1 c2 a b l (EL i c1092wc_code)) (oos c1 c2 a b l (EL i c1092wc_code))
                  (oou c1 c2 a b l (EL i c1092wc_code)) (oov c1 c2 a b l (EL i c1092wc_code)) l x y`;;

(* Lean: side_gt (private) *)
let C1092FPDA_SIDE_GT = C1092PSA_SIDE_GT;;
(* Lean: side_same (private) *)
let C1092FPDA_SIDE_SAME = C1092PSA_SIDE_SAME;;
(* Lean: marker_point (private) *)
let C1092FPDA_MARKER_POINT = C1092PSA_MARKER_POINT;;

(* Lean: exists_owner_frame *)
let C1092FPDA_EXISTS_OWNER_FRAME = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l
     ==> exists cC sC uC vC aC. cC * cC + sC * sC = &1 /\ &0 < aC /\
           c1092fpda_frame c1 c2 a b l i cC sC uC vC aC /\ &0 < cC /\ abs sC <= cC`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`ooc c1 c2 a b l (EL i c1092wc_code)`; `oos c1 c2 a b l (EL i c1092wc_code)`;
    `oou c1 c2 a b l (EL i c1092wc_code)`; `oov c1 c2 a b l (EL i c1092wc_code)`;
    `l:real`] CLF_CANONICAL_FRAME) THEN
  ASM_SIMP_TAC[OO_UNIT; OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  REWRITE_TAC[c1092fpda_frame] THEN MESON_TAC[]);;

let C1092FPDA_START_TAC =
  REWRITE_TAC[c1092fpda_frame] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV);;
let c1092fpda_lit s = rhs (concl (C1092PSA_CODE_CONV (parse_term s)));;
let c1092fpda_asm s = ASSUME (c1092fpda_lit s);;

let C1092FPDA_BOTTOMF = c1092psa_in 9 "&8 / &5" "&1";;
let C1092FPDA_ORIGIN = c1092psa_in 9 "&2" "&1";;
let C1092FPDA_HALF = c1092psa_in 0 "&1" "&3 / &2";;

(* Lean: corner_halfpoint_of_missing_bottom_origin *)
let C1092FPDA_CORNER_HALFPOINT_OF_MISSING_BOTTOM_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ ~%s ==> %s"
    C1092AE_P C1092AE_HYP C1092FPDA_BOTTOMF C1092FPDA_ORIGIN C1092FPDA_HALF),
  C1092FPDA_START_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  let boxy i = MATCH_MP C1092PSA_BOX_Y (c1092psa_box i) in
  let boxxy i = MATCH_MP C1092PSA_BOX_XY (c1092psa_box i) in
  let disj = REWRITE_RULE[GSYM ldisj] (c1092psa_apart 0 9) in
  let th = c1092psa_apply (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (SPECL (c1092psa_own 9 @ c1092psa_own 0 @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN)
    [c1092psa_unit 9; c1092psa_unit 0; c1092psa_pos (); c1092psa_side (); REFL `l:real`;
     boxy 9; boxxy 0; c1092psa_seed 9 (`&2`, `&457 / &500`); c1092fpda_asm C1092FPDA_BOTTOMF;
     c1092psa_seed 0 (`&1`, `&457 / &500`); c1092psa_seed 0 (`&1`, `&1`);
     c1092fpda_asm ("~" ^ C1092FPDA_HALF); disj] in
  UNDISCH_TAC (c1092fpda_lit ("~" ^ C1092FPDA_ORIGIN)) THEN REWRITE_TAC[th]);;

let C1092FPDA_P = c1092psa_in 4 "&1" "&87 / &50";;
let C1092FPDA_G = c1092psa_in 4 "&1" "&8 / &5";;
let C1092FPDA_FORWARDC = c1092psa_in 4 "&87 / &50" "&2";;
let C1092FPDA_FORWARDJ = c1092psa_in 5 "&2" "&87 / &50";;
let C1092FPDA_SQC = "cC * cC + sC * sC = &1 /\\ &0 < aC";;
let C1092FPDA_SQJ = "cJ * cJ + sJ * sJ = &1 /\\ &0 < aJ";;
let C1092FPDA_FRC = "c1092fpda_frame c1 c2 a b l 4 cC sC uC vC aC";;
let C1092FPDA_FRJ = "c1092fpda_frame c1 c2 a b l 5 cJ sJ uJ vJ aJ";;

(* Lean: predecessor_of_missing_bottom_origin *)
let C1092FPDA_PREDECESSOR_OF_MISSING_BOTTOM_ORIGIN = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ ~%s /\\ %s /\\ %s
      ==> c1092fpdf_predecessor cC sC uC vC aC"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092FPDA_BOTTOMF C1092FPDA_P C1092FPDA_G C1092FPDA_FORWARDC
    C1092FPDA_ORIGIN C1092FPDA_SQC C1092FPDA_FRC),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092FPDA_CORNER_HALFPOINT_OF_MISSING_BOTTOM_ORIGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC (parse_term C1092FPDA_FRC) THEN REWRITE_TAC[c1092fpda_frame] THEN STRIP_TAC THEN
  REWRITE_TAC[c1092fpdf_predecessor] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  let wa = c1092psa_wa () in
  REWRITE_TAC[c1092fpda_asm C1092FPDA_P; c1092fpda_asm C1092FPDA_G; c1092fpda_asm C1092FPDA_FORWARDC;
    c1092psa_seed 4 (`&33 / &20`, `&33 / &20`);
    c1092psa_excl 4 0 (c1092fpda_asm C1092FPDA_HALF);
    c1092psa_excl 4 7 (c1092psa_seed 7 (`&33 / &20`, `&47 / &20`));
    c1092psa_excl 4 8 (c1092psa_seed 8 (`&457 / &500`, `&2`));
    c1092psa_excl 4 8 (CONJUNCT1 wa)]);;

(* Lean: southeast_of_positive_predecessor *)
let C1092FPDA_SOUTHEAST_OF_POSITIVE_PREDECESSOR = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC cJ sJ uJ vJ aJ. %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ %s /\\
      %s /\\ %s /\\ %s /\\ %s /\\
      &0 < cC /\\ &0 <= sC /\\ sC <= cC /\\ &0 < cJ /\\ &0 <= sJ
      ==> ~%s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092FPDA_BOTTOMF C1092FPDA_P C1092FPDA_G C1092FPDA_FORWARDC
    C1092FPDA_FORWARDJ C1092FPDA_SQC C1092FPDA_SQJ C1092FPDA_FRC C1092FPDA_FRJ
    (c1092psa_in 5 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term C1092FPDA_ORIGIN) THENL
   [CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    ACCEPT_TAC(c1092psa_excl 5 9 (c1092fpda_asm C1092FPDA_ORIGIN));
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL C1092FPDA_PREDECESSOR_OF_MISSING_BOTTOM_ORIGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] OO_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> can (term_match [] `c1092fpda_frame c1 c2 a b l i cC sC uC vC aC`) (concl th)))) THEN
  REWRITE_TAC[c1092fpda_frame] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~linside cJ sJ uJ vJ aJ (&2) (&1)` MP_TAC THENL
   [MATCH_MP_TAC (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                         `cJ:real`; `sJ:real`; `uJ:real`; `vJ:real`; `aJ:real`] C1092FPDL_PREVIOUS_ORIGIN_EXCLUDED) THEN
    ASM_REWRITE_TAC[ldisj] THEN
    CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    ASM_REWRITE_TAC[c1092psa_seed 5 (`&47 / &20`, `&33 / &20`)] THEN
    REWRITE_TAC[REWRITE_RULE[ldisj] (MP (SPECL C1092MPPE_V
      (oo_apart `c1092wc_family` 256 512)) (c1092psa_hh ()))];
    ASM_REWRITE_TAC[]]);;

(* Lean: NonpositiveHalfpoint *)
let c1092fpda_nonpositiveHalfpoint = new_definition
 `c1092fpda_nonpositiveHalfpoint (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real) <=>
    forall cC sC uC vC aC. cC * cC + sC * sC = &1 /\ &0 < aC /\
      c1092fpda_frame c1 c2 a b l 4 cC sC uC vC aC /\ &0 < cC /\ abs sC <= cC /\ sC <= &0
      ==> linside (ooc c1 c2 a b l (EL 4 c1092wc_code)) (oos c1 c2 a b l (EL 4 c1092wc_code))
                  (oou c1 c2 a b l (EL 4 c1092wc_code)) (oov c1 c2 a b l (EL 4 c1092wc_code)) l
                  (&1) (&3 / &2)`;;

(* Lean: southeast_of_nonpositive_halfpoint *)
let C1092FPDA_SOUTHEAST_OF_NONPOSITIVE_HALFPOINT = prove
 (parse_term (Printf.sprintf "!%s cJ sJ uJ vJ aJ. %s /\\ %s /\\ (!k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k) /\\
      %s /\\ %s /\\ %s /\\ %s /\\ %s /\\ &0 < cJ /\\ &0 <= sJ /\\
      c1092fpda_nonpositiveHalfpoint c1 c2 a b l
      ==> ~%s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092FPDA_P C1092FPDA_G C1092FPDA_FORWARDJ
    C1092FPDA_SQJ C1092FPDA_FRJ (c1092psa_in 5 "&2" "&1")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MOM_ORDINARY_WALLS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term C1092FPDA_ORIGIN) THENL
   [CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
    ACCEPT_TAC(c1092psa_excl 5 9 (c1092fpda_asm C1092FPDA_ORIGIN));
    ALL_TAC] THEN
  SUBGOAL_THEN (parse_term C1092FPDA_FORWARDC) ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC (parse_term ("~" ^ C1092FPDA_ORIGIN)) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC C1092PSA_BOTTOM_ORIGIN_OF_MISSING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `4`]
    C1092FPDA_EXISTS_OWNER_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC))
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC (parse_term ("~" ^ C1092FPDA_ORIGIN)) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC C1092PSA_BOTTOM_ORIGIN_OF_HALFPOINT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `c1092fpda_nonpositiveHalfpoint c1 c2 a b l` THEN
    REWRITE_TAC[c1092fpda_nonpositiveHalfpoint] THEN DISCH_THEN MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC C1092FPDA_SOUTHEAST_OF_POSITIVE_PREDECESSOR THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cJ:real`; `sJ:real`; `uJ:real`; `vJ:real`; `aJ:real`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `abs sC <= cC` THEN UNDISCH_TAC `&0 < sC` THEN REAL_ARITH_TAC);;

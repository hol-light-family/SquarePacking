(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NegativeCenterSupports.lean          *)
(* (N12Compact.C1092MMMPNegativeCenterSupports).  Support supplied by the    *)
(* genuine centre cut and physical left wall.  L = cL sL uL vL aL,           *)
(* K = cK sK uK vK aK; centerX/centerY are lcx/lcy; square_support_bound is  *)
(* C1092MPWS_SQUARE_SUPPORT_BOUND; CenterCorner tools C1092MMCC_*; upward    *)
(* and negative_support C1092MCSUP_*; SAT step ABT_FOUR_AXES.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_CenterCorner.ml";;
needs "n12/geometry/CP_C1092_MMMP_PhysicalWallSupport.ml";;

let C1092MNCS_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092MNCS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [TRY(MATCH_ACCEPT_TAC REAL_LE_SQUARE) THEN
   REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092MNCS_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

let C1092MNCS_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let C1092MNCS_CANCEL = prove
 (`forall k x. &0 < k /\ &0 <= k * x ==> &0 <= x`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:real`; `--x`] REAL_LT_MUL) THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REAL_ARITH_TAC);;

(* Lean: radius_scalar (private) *)
let C1092MNCS_RADIUS_SCALAR = prove
 (`forall d r c s. c977cc_normal d r /\ c977cc_normal c s
     ==> c + s <= s * (d + r) + abs(s * d - c * r) + (s * r + c * d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MNCS_NORMAL_TAC THEN
  C1092MNCS_PROD `&0 <= (&1 - d) * (&1 - r)` THEN
  C1092MNCS_PROD `&0 <= r * r` THEN
  C1092MNCS_PROD `&0 <= c * ((&1 - d) * (&1 - r) + r * r)` THEN
  SUBGOAL_THEN `d * (d * d + r * r) = d /\ c * (d * d + r * r) = c` STRIP_ASSUME_TAC THENL
  [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= s * d - c * r` THENL
  [ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
   C1092MNCS_PROD `&0 <= (s * d - c * r) * (&2 * (d + r) - &1)` THEN
   MP_TAC(SPECL [`d:real`; `s * (d + r) + (s * d - c * r) + (s * r + c * d) - c - s`]
     C1092MNCS_CANCEL) THEN
   ANTS_TAC THENL [CONJ_TAC THEN C1092MNCS_LP_TAC; REAL_ARITH_TAC];
   ASM_SIMP_TAC[REAL_ARITH `~(&0 <= x) ==> abs x = --x`] THEN
   ASM_CASES_TAC `&0 <= &2 * r - &1` THENL
   [C1092MNCS_PROD `&0 <= c * (d + r - &1)` THEN C1092MNCS_PROD `&0 <= s * (&2 * r - &1)` THEN
    C1092MNCS_LP_TAC;
    C1092MNCS_PROD `&0 <= --(s * d - c * r) * --(&2 * r - &1)` THEN
    MP_TAC(SPECL [`d:real`; `s * (d + r) - (s * d - c * r) + (s * r + c * d) - c - s`]
      C1092MNCS_CANCEL) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C1092MNCS_LP_TAC; REAL_ARITH_TAC]]]);;

(* Lean: up_right *)
let C1092MNCS_UP_RIGHT = prove
 (`forall cL sL uL vL aL c s.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ c977cc_normal cL (--sL) /\
     (forall x y. linside cL sL uL vL aL x y ==> --(&1) <= x) /\ &0 <= lcy cL sL uL vL aL /\
     c977cc_normal c s
     ==> aL * (c + s) / &2 - s <= ABT_upper cL sL uL vL aL s c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `--sL:real`; `c:real`; `s:real`] C1092MNCS_RADIUS_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `--(&1)`; `&0`; `&1`]
    C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`] o check (is_forall o concl)) THEN
   ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; DISCH_TAC] THEN
  C1092MNCS_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[tss_support_radius]) THEN
  SUBGOAL_THEN `abs(-- &1 * cL + &0 * sL) = cL /\ abs(-- -- &1 * sL + &0 * cL) = --sL`
  (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ABT_upper; tss_support_radius] THEN
  C1092MNCS_PROD `&0 <= s * --sL` THEN C1092MNCS_PROD `&0 <= c * cL` THEN
  SUBGOAL_THEN `abs(--s * sL + c * cL) = s * --sL + c * cL /\
                abs(s * cL + c * sL) = abs(s * cL - c * --sL)` (fun th -> REWRITE_TAC[th]) THENL
  [CONJ_TAC THENL [RASM_ARITH_TAC; AP_TERM_TAC THEN REAL_ARITH_TAC]; ALL_TAC] THEN
  C1092MNCS_PROD `&0 <= s * (lcx cL sL uL vL aL - (--(&1) + aL * (cL + --sL) / &2))` THEN
  C1092MNCS_PROD `&0 <= c * lcy cL sL uL vL aL` THEN
  C1092MNCS_PROD `&0 <= (aL / &2) * ((s * (cL + --sL) + abs(s * cL - c * --sL) +
                                        (s * --sL + c * cL)) - (c + s))` THEN
  C1092MNCS_LP_TAC);;

(* Lean: left_blocked *)
let C1092MNCS_LEFT_BLOCKED = C1092MMCC_LEFT_BLOCKED;;

(* Lean: reverse_blocked (private) *)
let C1092MNCS_REVERSE_BLOCKED = C1092MCA_REVERSE_BLOCKED;;

(* Lean: alternatives *)
let C1092MNCS_ALTERNATIVES = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL (--sL) /\ &0 < cK /\
     lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     linside cL sL uL vL aL (&0) (&2 / &5) /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> vL + aL <= ABT_lower cK sK uK vK aK (--sL) cL \/
         ABT_upper cL sL uL vL aL cK sK <= uK \/
         ABT_upper cL sL uL vL aL (--sK) cK <= vK`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aL:real = aK`)) THEN
  SUBGOAL_THEN `&0 < cL /\ sL <= &0` STRIP_ASSUME_TAC THENL
  [FIRST_ASSUM(MP_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
   FIRST_ASSUM(MP_TAC o REWRITE_RULE[c977cc_normal] o
     check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cL pow 2 + sL pow 2 = &1 /\ (--sL) pow 2 + cL pow 2 = &1 /\
                (--cL) pow 2 + (--sL) pow 2 = &1 /\
                cK pow 2 + sK pow 2 = &1 /\ (--sK) pow 2 + cK pow 2 = &1 /\
                (--cK) pow 2 + (--sK) pow 2 = &1` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] ABT_FOUR_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  let sqs = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
             `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`] in
  let lb nx ny =
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC C1092MNCS_LEFT_BLOCKED THEN
    MAP_EVERY EXISTS_TAC (sqs @ [nx; ny]) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC
  and rb nx ny =
    MATCH_MP_TAC(TAUT `false ==> p`) THEN
    MATCH_MP_TAC C1092MNCS_REVERSE_BLOCKED THEN
    MAP_EVERY EXISTS_TAC (sqs @ [nx; ny]) THEN
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC
  and negs nx ny =
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; nx; ny]
      C1092MCSUP_NEGATIVE_SUPPORT) THEN
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aL:real`; nx; ny]
      C1092MCSUP_NEGATIVE_SUPPORT) THEN
    REPEAT STRIP_TAC in
  REWRITE_TAC[IMP_CONJ] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [MATCH_MP_TAC(TAUT `false ==> p`) THEN
   MP_TAC(SPECL (sqs @ [`cL:real`; `sL:real`]) C1092MCSUP_UPWARD) THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
   negs `cL:real` `sL:real` THEN lb `--cL:real` `--sL:real`;
   ASM_REWRITE_TAC[];
   rb `--sL:real` `cL:real`;
   ASM_REWRITE_TAC[];
   negs `cK:real` `sK:real` THEN lb `--cK:real` `--sK:real`;
   ASM_REWRITE_TAC[];
   rb `--sK:real` `cK:real`]);;

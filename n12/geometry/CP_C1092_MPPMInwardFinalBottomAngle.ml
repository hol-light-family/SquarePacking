(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalBottomAngle.lean          *)
(* (N12Compact.C1092MPPMInwardFinal.BottomAngle; Lean header: "Source only").*)
(* INWARD-BOTTOM-ANGLE, Theorem 1.  Conventions of                           *)
(* MPPMInwardFinalBottomData.ml (Input is c1092ifbd_input, hypotheses        *)
(* C1092IFBD_HYP); half is C1092WPS_half; Normal is c977cc_normal.           *)
(* Tag C1092IFBA_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomPositive.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBottomNegative.ml";;

let C1092IFBA_POS_C = prove
 (`forall c s. c * c + s * s = &1 /\ abs s <= c ==> &0 < c`,
  REWRITE_TAC[REAL_ABS_BOUNDS] THEN REPEAT STRIP_TAC THEN NLIN_TAC []);;

(* Lean: canonical_center_frame (private) *)
let C1092IFBA_CANONICAL_CENTER_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 < c' /\ abs s' <= c' /\ a' = a /\
           lcx c' s' u' v' a' = lcx c s u v a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)`,
  let tac wits = MAP_EVERY EXISTS_TAC wits THEN
    REWRITE_TAC[linside; lcx] THEN REPEAT CONJ_TAC THEN
    TRY(REPEAT GEN_TAC THEN ASM_REAL_ARITH_TAC) THEN
    MATCH_MP_TAC C1092IFBA_POS_C THEN EXISTS_TAC (el 1 wits) THEN ASM_REAL_ARITH_TAC in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `abs s <= c` THENL
   [tac [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]; ALL_TAC] THEN
  ASM_CASES_TAC `abs c <= --s` THENL
   [tac [`--s:real`; `c:real`; `v:real`; `--u - a:real`; `a:real`]; ALL_TAC] THEN
  ASM_CASES_TAC `abs c <= s` THENL
   [tac [`s:real`; `--c:real`; `--v - a:real`; `u:real`; `a:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `abs s <= --c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  tac [`--c:real`; `--s:real`; `--u - a:real`; `--v - a:real`; `a:real`]);;

(* Lean: polynomial *)
let C1092IFBA_POLYNOMIAL = prove
 (parse_term (Printf.sprintf
   "!%s. %s ==> &0 < C1092WPS_half cC (--sC) pow 2 - &2 * C1092WPS_half cC (--sC) + &1 / &5"
   C1092IFBD_VARS C1092IFBD_HYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C1092IFBA_CANONICAL_CENTER_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cD:real` (X_CHOOSE_THEN `sD:real` (X_CHOOSE_THEN `uD:real`
    (X_CHOOSE_THEN `vD:real` (X_CHOOSE_THEN `aD:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `c1092ifbd_input cC sC uC vC aC cD sD uD vD aD` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092ifbd_input cC sC uC vC aC cB sB uB vB aB` THEN
    ASM_REWRITE_TAC[c1092ifbd_input; ldisj] THEN SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sD` THENL
   [MATCH_MP_TAC C1092IFBP_NONNEGATIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                          `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC C1092IFBN_NONPOSITIVE_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                          `cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: angle *)
let C1092IFBA_ANGLE = prove
 (parse_term (Printf.sprintf
   "!%s. %s ==> &0 < C1092WPS_half cC (--sC) /\\ C1092WPS_half cC (--sC) < &1 - &2 * sqrt(&5) / &5 /\\ C1092WPS_half cC (--sC) < &53 / &500"
   C1092IFBD_VARS C1092IFBD_HYP),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092IFBD_CENTRAL_FACES) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092IFBA_POLYNOMIAL) THEN
  ASM_REWRITE_TAC[c1092ifbd_faces] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `c977cc_normal cC (--sC)` ASSUME_TAC THENL
   [UNDISCH_TAC `c1092ifbd_input cC sC uC vC aC cB sB uB vB aB` THEN
    REWRITE_TAC[c1092ifbd_input] THEN STRIP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C1092IFBS_THRESHOLD) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[C1092WPS_half] THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC);;

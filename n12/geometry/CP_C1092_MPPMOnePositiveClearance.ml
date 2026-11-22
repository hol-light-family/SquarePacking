(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOnePositiveClearance.lean             *)
(* (N12Compact.C1092MPPMOnePositive).  ONE-POSITIVE-CONTINUOUS-ENDING Lemma *)
(* 2, literal physical input and clearance.  Squares C, E, B are            *)
(* c s u v a, cE sE uE vE aE, cB sB uB vB aB with their OpenSquare          *)
(* invariants as explicit hypotheses.  PositiveMissingInput is              *)
(* c1092opc_input; AllNonpositive.Core / faces / above_bar are              *)
(* c1092anc_core / C1092ANC_FACES / C1092ANC_ABOVE_BAR; Normal is           *)
(* c977cc_normal; CrosspointSupport.half is c1092mcbh_half; WallProfile.    *)
(* vertex is OCWPVG_VERTEX; ABTransverse.upper is ABT_upper (supportRadius  *)
(* tss_support_radius); centerX / centerY are lcx / lcy.  The local lets    *)
(* A, X, Y, c, s, d, t, k, ell are written out (Lean s = --s here).         *)
(* Tag C1092OPC_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMOnePositiveScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMAllNonpositiveCore.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareGeometry.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let C1092OPC_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092OPC_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092OPC_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

(* Lean: PositiveMissingInput (structure) *)
let c1092opc_input = new_definition
 `c1092opc_input (c:real) (s:real) (u:real) (v:real) (a:real)
                 (cE:real) (sE:real) (uE:real) (vE:real) (aE:real)
                 (cB:real) (sB:real) (uB:real) (vB:real) (aB:real) <=>
    c1092anc_core c s u v a /\ a = aE /\ &97 / &100 < c /\ &4 * --s < c /\
    v + a < &43 / &500 /\ c977cc_normal cE sE /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&0) (--(&1 / &2)) /\
    --cE - sE <= vE /\ uE + aE <= cE - (&14 / &25) * sE /\
    &13 / &87 <= c1092mcbh_half cE sE /\
    (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
    ldisj c s u v a cE sE uE vE aE /\ ldisj c s u v a cB sB uB vB aB`;;

let C1092OPC_SETUP_TAC =
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o
    check (fun th -> can (term_match [] `c1092anc_core c s u v a`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c (--s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c (--s)`)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> can (term_match [] `linside c s u v a x y`) (concl th)) ths));;

(* from ldisj and a point inside the other square: the point (x, y) of the first square, *)
(* which the goal F then contradicts via the strict inequalities *)
let C1092OPC_APART_TAC ldisj_tm (x, y) =
  FIRST_ASSUM(MP_TAC o SPECL [x; y] o REWRITE_RULE[ldisj] o
    check (fun th -> concl th = ldisj_tm)) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[linside] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN C1092OPC_LP_TAC;;

(* Lean: positive_missing_clearance *)
let C1092OPC_POSITIVE_MISSING_CLEARANCE = prove
 (`forall c s u v a cE sE uE vE aE cB sB uB vB aB.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092opc_input c s u v a cE sE uE vE aE cB sB uB vB aB
     ==> u + a <= --s / &2 /\ --(&1) < s * (u + a) + c * v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092opc_input; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aE`)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  C1092OPC_SETUP_TAC THEN
  SUBGOAL_THEN `--s < &1 / &4` ASSUME_TAC THENL [C1092OPC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= --s / &2` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092OPC_APART_TAC `ldisj c s u v a cE sE uE vE a` (`&0`, `--(&1 / &2)`); ALL_TAC] THEN
  SUBGOAL_THEN `linside cB sB uB vB aB (--(&14 / &25)) (--(&1))` ASSUME_TAC THENL
  [FIRST_ASSUM(fun th -> if is_forall(concl th) then MP_TAC(SPEC `--(&14 / &25)` th)
                         else NO_TAC) THEN
   CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `--c + (&14 / &25) * s <= v` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092OPC_APART_TAC `ldisj c s u v a cB sB uB vB aB` (`--(&14 / &25)`, `--(&1)`);
   ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `u + a`; `v:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  C1092OPC_PROD `&0 <= c * (u - --c)` THEN
  C1092OPC_PROD `&0 <= --s * (v - (--c + (&14 / &25) * s))` THEN
  C1092OPC_PROD `&0 < c * (a - &1)` THEN
  C1092OPC_PROD `&0 <= --s * (&1 - c)` THEN
  SUBGOAL_THEN `&0 <= s * s` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  SUBGOAL_THEN `--(&14 / &25) < c * (u + a) - s * v` ASSUME_TAC THENL
  [C1092OPC_LP_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c * (c * (u + a) - s * v) + s * (s * (u + a) + c * v) = u + a`
    ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092OPC_PROD `&0 <= --s * (--(&1) - (s * (u + a) + c * v))` THEN
  SUBGOAL_THEN `c * (c * (u + a) - s * v) <= &0` ASSUME_TAC THENL
  [C1092OPC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c * (u + a) - s * v <= &0` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092OPC_PROD `&0 < c * (c * (u + a) - s * v)` THEN C1092OPC_LP_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `c * (u + a) - s * v`; `s * (u + a) + c * v`] C1092ANC_ABOVE_BAR) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_TAC THEN C1092OPC_LP_TAC);;

(* Lean: positive_missing_upward *)
let C1092OPC_POSITIVE_MISSING_UPWARD = prove
 (`forall c s u v a cE sE uE vE aE cB sB uB vB aB.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092opc_input c s u v a cE sE uE vE aE cB sB uB vB aB
     ==> --sE / &2 < ABT_upper c s u v a cE sE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092OPC_POSITIVE_MISSING_CLEARANCE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c1092opc_input] o
    check (fun th -> can (term_match [] `c1092opc_input c s u v a cE sE uE vE aE cB sB uB vB aB`)
                         (concl th))) THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aE`)) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o
    check (fun th -> can (term_match [] `c1092anc_core c s u v a`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c (--s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  SUBGOAL_THEN `--s < &1 / &4` ASSUME_TAC THENL [C1092OPC_LP_TAC; ALL_TAC] THEN
  C1092OPC_PROD `&0 < cE * (c + s)` THEN C1092OPC_PROD `&0 <= --s * (cE - sE)` THEN
  SUBGOAL_THEN `&0 < cE * c + sE * s` ASSUME_TAC THENL [C1092OPC_LP_TAC; ALL_TAC] THEN
  C1092OPC_PROD `&0 < --s * cE` THEN C1092OPC_PROD `&0 <= c * sE` THEN
  SUBGOAL_THEN `&0 < --cE * s + sE * c` ASSUME_TAC THENL [C1092OPC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092OPC_PROD `&0 < --s * --s` THEN C1092OPC_PROD `&0 <= (c - &1) * c` THEN
   C1092OPC_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) + a * (c - s) / &2 < lcy c s u v a` ASSUME_TAC THENL
  [REWRITE_TAC[lcy] THEN C1092OPC_LP_TAC; ALL_TAC] THEN
  REWRITE_TAC[ABT_upper; tss_support_radius] THEN
  SUBGOAL_THEN `abs(cE * c + sE * s) = cE * c + sE * s /\
                abs(--cE * s + sE * c) = --cE * s + sE * c`
    (fun th -> REWRITE_TAC[th]) THENL
  [REWRITE_TAC[REAL_ABS_REFL] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `cE * (c * lcx c s u v a + s * lcy c s u v a) = cE * (u + a / &2)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092OPC_PROD `&0 <= cE * (u + c)` THEN
  C1092OPC_PROD `&0 < (--cE * s + sE * c) * (lcy c s u v a - (--(&1) + a * (c - s) / &2))` THEN
  C1092OPC_PROD `&0 < (--cE * s + sE * c) * (c - s)` THEN
  C1092OPC_PROD `&0 < c * ((cE * c + sE * s) + (--cE * s + sE * c))` THEN
  SUBGOAL_THEN `&0 < (--cE * s + sE * c) * (c - s) + cE +
                     c * ((cE * c + sE * s) + (--cE * s + sE * c))` ASSUME_TAC THENL
  [C1092OPC_LP_TAC; ALL_TAC] THEN
  C1092OPC_PROD `&0 < (a - &1) * ((--cE * s + sE * c) * (c - s) + cE +
                                  c * ((cE * c + sE * s) + (--cE * s + sE * c)))` THEN
  SUBGOAL_THEN
   `--c * cE - (--cE * s + sE * c) +
    ((--cE * s + sE * c) * (c - s) + cE + c * ((cE * c + sE * s) + (--cE * s + sE * c))) / &2 =
    (&1 - c) * (cE * (&1 + s) - c * sE)` ASSUME_TAC THENL
  [UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092OPC_PROD `&0 < (&1 - c) * cE * (&1 + s)` THEN
  C1092OPC_PROD `&0 <= c * sE * (c - &1 / &2)` THEN
  SUBGOAL_THEN `&0 < c * ((cE * lcx c s u v a + sE * lcy c s u v a +
     a / &2 * ((cE * c + sE * s) + (--cE * s + sE * c))) + sE / &2)` ASSUME_TAC THENL
  [C1092OPC_LP_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `c * ((cE * lcx c s u v a + sE * lcy c s u v a +
     a / &2 * ((cE * c + sE * s) + (--cE * s + sE * c))) + sE / &2) <= &0` MP_TAC THENL
  [REWRITE_TAC[REAL_ARITH `c * x <= &0 <=> &0 <= c * --x`] THEN
   MATCH_MP_TAC REAL_LE_MUL THEN C1092OPC_LP_TAC;
   DISCH_TAC THEN C1092OPC_LP_TAC]);;

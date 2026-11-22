(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMSteepPositiveThreeSquareGeometry.lean *)
(* (namespace N12Compact.C1092MPPMSteepPositiveThreeSquare).  Simultaneous   *)
(* actual-side support caps and the elimination of the boundary center,     *)
(* STEEP-POSITIVE-THREE-SQUARE-REDUCTION sections 3--4.                      *)
(* Squares C, E, B are (cC, ..), (cE, ..), (cB, ..).  Input: c1092spts_input;*)
(* Quarter, k, kC, deltaC, kE, deltaE, C0, E0, FC, FE, G00..G11:             *)
(* c1092mcs_*; lower/upper: ABT_lower/ABT_upper; centerX: lcx;               *)
(* lower_nn/np/pn: C1092WS_LOWER_NN/NP/PN; ShallowBoundarySupport.          *)
(* bottom_center / width0: C1092SBS_BOTTOM_CENTER / c1092sbs_width0;         *)
(* S12.exists_positive_frame: WCB_EXISTS_POSITIVE_FRAME.                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMSteepPositiveThreeSquareData.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveRetainingSteepScalars.ml";;

let C1092SPTG_V =
  [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
   `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
   `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* unpack Input and Quarter, identify the three sides with aC, unfold Normal *)
let C1092SPTG_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spts_input] o
    check (can (term_match [] `c1092spts_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  TRY(FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter x y`) o concl))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C1092PRS_NORMAL_TAC THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
    check (can (term_match [] `linside c s u v a x y`) o concl)));;

let C1092SPTG_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;

(* a product fact, each factor by linear arithmetic, put into the goal *)
let C1092SPTG_PROD_MP tm = SUBGOAL_THEN tm MP_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092SPTG_LIN; ALL_TAC];;
let C1092SPTG_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092SPTG_LIN; ALL_TAC];;

let C1092SPTG_DEFS = [c1092mcs_k; c1092mcs_kC; c1092mcs_deltaC; c1092mcs_kE;
                      c1092mcs_deltaE; c1092mcs_C0; c1092mcs_E0];;

(* Lean: dot_nonnegative (private) *)
let C1092SPTG_DOT_NONNEGATIVE = prove
 (`forall c s h r. c977cc_normal c s /\ c1092mcs_quarter h r ==> &0 <= c * h + s * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter x y`) o concl)) THEN
  MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
  RASM_ARITH_TAC);;

let C1092SPTG_KC_TAC =
  SUBGOAL_THEN `&0 <= c1092mcs_kC cC sC cB sB /\ &0 <= c1092mcs_kE cE sE cB sB`
    STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcs_kC; c1092mcs_kE] THEN CONJ_TAC THEN
    MATCH_MP_TAC C1092SPTG_DOT_NONNEGATIVE THEN
    ASM_REWRITE_TAC[c1092mcs_quarter];
    ALL_TAC];;

(* Lean: central_cap *)
let C1092SPTG_CENTRAL_CAP = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB
     ==> ABT_lower cC sC uC vC aC (--sB) cB <=
         c1092mcs_FC cC sC cB sB -
         (aC - &1) * (c1092mcs_kC cC sC cB sB + abs(c1092mcs_deltaC cC sC cB sB))`,
  C1092SPTG_OPEN_TAC THEN C1092SPTG_KC_TAC THEN
  SUBGOAL_THEN `--sB * cC + cB * sC = --c1092mcs_deltaC cC sC cB sB /\
                -- --sB * sC + cB * cC = c1092mcs_kC cC sC cB sB` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcs_deltaC; c1092mcs_kC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092SPTG_PROD `&0 <= c1092mcs_kC cC sC cB sB * ((&543 / &500) * sC - (vC + aC))` THEN
  REWRITE_TAC[c1092mcs_FC; real_abs] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--c1092mcs_deltaC cC sC cB sB`; `c1092mcs_kC cC sC cB sB`] C1092WS_LOWER_NP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPTG_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092SPTG_PROD `&0 <= c1092mcs_deltaC cC sC cB sB * (uC - (--cC - sC))` THEN
    C1092SPTG_LIN;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB`; `cB:real`;
                  `--c1092mcs_deltaC cC sC cB sB`; `c1092mcs_kC cC sC cB sB`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPTG_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092SPTG_PROD `&0 <= --c1092mcs_deltaC cC sC cB sB * (--cC / &2 - (uC + aC))` THEN
    C1092SPTG_LIN]);;

(* Lean: recipient_cap *)
let C1092SPTG_RECIPIENT_CAP = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB
     ==> ABT_lower cE sE uE vE aE cB sB <=
         c1092mcs_FE cE sE cB sB - (aC - &1) * c1092mcs_kE cE sE cB sB`,
  C1092SPTG_OPEN_TAC THEN C1092SPTG_KC_TAC THEN
  SUBGOAL_THEN `cB * cE + sB * sE = c1092mcs_kE cE sE cB sB /\
                --cB * sE + sB * cE = c1092mcs_deltaE cE sE cB sB` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcs_deltaE; c1092mcs_kE] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C1092SPTG_PROD `&0 <= c1092mcs_kE cE sE cB sB * ((cE - (&14 / &25) * sE) - (uE + aC))` THEN
  REWRITE_TAC[c1092mcs_FE; c1092mcs_E0] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cB:real`; `sB:real`;
                  `c1092mcs_kE cE sE cB sB`; `c1092mcs_deltaE cE sE cB sB`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPTG_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092SPTG_PROD `&0 <= c1092mcs_deltaE cE sE cB sB *
                          ((--sE * &2 / &5 + cE * --(&1)) - vE)` THEN
    C1092SPTG_LIN;
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cB:real`; `sB:real`;
                  `c1092mcs_kE cE sE cB sB`; `c1092mcs_deltaE cE sE cB sB`] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPTG_LIN; DISCH_THEN SUBST1_TAC] THEN
    C1092SPTG_PROD `&0 <= --c1092mcs_deltaE cE sE cB sB * ((vE + aC) + cE / &2)` THEN
    C1092SPTG_LIN]);;

(* Lean: floor_upper *)
let C1092SPTG_FLOOR_UPPER = prove
 (`forall cB sB uB vB aB nx ny.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ c1092mcs_quarter cB sB /\
     (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\ &0 <= ny
     ==> nx * lcx cB sB uB vB aB - &2 * ny +
         (aB / &2) * (ny * (cB + sB) + abs(nx * cB + ny * sB) + abs(--nx * sB + ny * cB))
         <= ABT_upper cB sB uB vB aB nx ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter x y`) o concl)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092SBS_BOTTOM_CENTER) THEN
  ASM_REWRITE_TAC[c1092sbs_width0] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN DISCH_TAC THEN
  C1092SPTG_PROD `&0 <= ny * (lcy cB sB uB vB aB - (--(&2) + aB * (cB + sB) / &2))` THEN
  REWRITE_TAC[ABT_upper; tss_support_radius] THEN C1092SPTG_LIN);;

(* the projections of the four normals onto the boundary frame *)
let C1092SPTG_ABS_EQS = prove
 (`--sC * cB + cC * sB = c1092mcs_deltaC cC sC cB sB /\
   -- --sC * sB + cC * cB = c1092mcs_kC cC sC cB sB /\
   cE * cB + sE * sB = c1092mcs_kE cE sE cB sB /\
   --cE * sB + sE * cB = --c1092mcs_deltaE cE sE cB sB /\
   --sB * cB + cB * sB = &0 /\
   -- --sB * sB + cB * cB = cB * cB + sB * sB /\
   --cB * sB + sB * cB = &0`,
  REWRITE_TAC[c1092mcs_deltaC; c1092mcs_kC; c1092mcs_kE; c1092mcs_deltaE] THEN
  REAL_ARITH_TAC);;

(* Lean: boundary_supports (private) *)
let C1092SPTG_BOUNDARY_SUPPORTS = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB
     ==> --sC * lcx cB sB uB vB aB - &2 * cC +
           (aC / &2) * (cC * (cB + sB) + c1092mcs_kC cC sC cB sB +
                        abs(c1092mcs_deltaC cC sC cB sB))
           <= ABT_upper cB sB uB vB aB (--sC) cC /\
         cE * lcx cB sB uB vB aB - &2 * sE +
           (aC / &2) * (sE * (cB + sB) + c1092mcs_kE cE sE cB sB +
                        abs(c1092mcs_deltaE cE sE cB sB))
           <= ABT_upper cB sB uB vB aB cE sE /\
         --sB * lcx cB sB uB vB aB - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)
           <= ABT_upper cB sB uB vB aB (--sB) cB /\
         cB * lcx cB sB uB vB aB - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)
           <= ABT_upper cB sB uB vB aB cB sB`,
  C1092SPTG_OPEN_TAC THEN C1092SPTG_KC_TAC THEN
  REPEAT CONJ_TAC THEN
  W(fun (_,w) ->
    let nx, ny = match snd(strip_comb(rand w)) with
                   [_;_;_;_;_;x;y] -> x, y | _ -> failwith "supports" in
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; nx; ny]
      C1092SPTG_FLOOR_UPPER)) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPTG_LIN; ALL_TAC]) THEN
  CONV_TAC(SUBS_CONV (CONJUNCTS C1092SPTG_ABS_EQS)) THEN
  REWRITE_TAC[REAL_ABS_NEG; REAL_ABS_0] THEN
  ASM_REWRITE_TAC[REAL_ABS_NUM] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN
  MATCH_MP_TAC(REAL_ARITH `a = b ==> b <= c ==> a <= c`) THEN
  REAL_ARITH_TAC);;

(* Lean: H00, H01, H10, H11 (definitions) *)
let c1092sptg_H00 = new_definition
 `c1092sptg_H00 (c:real) s d t h r =
    (c1092mcs_k c s d t * (h + r) + d * (c1092mcs_kC c s h r + abs(c1092mcs_deltaC c s h r)) +
     s * (c1092mcs_kE d t h r + abs(c1092mcs_deltaE d t h r))) / &2 + d + s`;;
let c1092sptg_H01 = new_definition
 `c1092sptg_H01 (c:real) s (d:real) t h r =
    (c1092mcs_kC c s h r * (h + r) + h * (c1092mcs_kC c s h r + abs(c1092mcs_deltaC c s h r)) +
     s) / &2 + h + s * c1092mcs_kE d t h r`;;
let c1092sptg_H10 = new_definition
 `c1092sptg_H10 (c:real) s d t h r =
    (c1092mcs_kE d t h r * (h + r) + d + r * (c1092mcs_kE d t h r + abs(c1092mcs_deltaE d t h r))) /
    &2 + d * (c1092mcs_kC c s h r + abs(c1092mcs_deltaC c s h r)) + r`;;
let c1092sptg_H11 = new_definition
 `c1092sptg_H11 (c:real) s d t h r =
    h + r + h * (c1092mcs_kC c s h r + abs(c1092mcs_deltaC c s h r)) +
    r * c1092mcs_kE d t h r`;;

let C1092SPTG_QUARTER_SUM = prove
 (`forall h r. &0 <= h /\ &0 <= r /\ h pow 2 + r pow 2 = &1 ==> &1 <= h + r`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC []);;

(* Lean: side_coefficients (private) *)
let C1092SPTG_SIDE_COEFFICIENTS = prove
 (`forall c s d t h r.
     c977cc_normal c s /\ &3 / &5 <= s /\ c977cc_normal d t /\ c1092mcs_quarter h r
     ==> &0 < c1092sptg_H00 c s d t h r /\ &0 < c1092sptg_H01 c s d t h r /\
         &0 < c1092sptg_H10 c s d t h r /\ &0 < c1092sptg_H11 c s d t h r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= c1092mcs_kC c s h r /\ &0 <= c1092mcs_kE d t h r` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcs_kC; c1092mcs_kE] THEN CONJ_TAC THEN
    MATCH_MP_TAC C1092SPTG_DOT_NONNEGATIVE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  C1092PRS_NORMAL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter x y`) o concl)) THEN
  SUBGOAL_THEN `&0 < c1092mcs_k c s d t` ASSUME_TAC THENL
   [REWRITE_TAC[c1092mcs_k] THEN
    C1092SPTG_PROD `&0 < c * d` THEN C1092SPTG_PROD `&0 <= s * t` THEN C1092SPTG_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= h + r` ASSUME_TAC THENL
   [MATCH_MP_TAC C1092SPTG_QUARTER_SUM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASSUME_TAC(SPEC `c1092mcs_deltaC c s h r` REAL_ABS_POS) THEN
  ASSUME_TAC(SPEC `c1092mcs_deltaE d t h r` REAL_ABS_POS) THEN
  C1092SPTG_PROD `&0 <= c1092mcs_k c s d t * (h + r)` THEN
  C1092SPTG_PROD `&0 <= d * (c1092mcs_kC c s h r + abs(c1092mcs_deltaC c s h r))` THEN
  C1092SPTG_PROD `&0 <= s * (c1092mcs_kE d t h r + abs(c1092mcs_deltaE d t h r))` THEN
  C1092SPTG_PROD `&0 <= c1092mcs_kC c s h r * (h + r)` THEN
  C1092SPTG_PROD `&0 <= h * (c1092mcs_kC c s h r + abs(c1092mcs_deltaC c s h r))` THEN
  C1092SPTG_PROD `&0 <= s * c1092mcs_kE d t h r` THEN
  C1092SPTG_PROD `&0 <= c1092mcs_kE d t h r * (h + r)` THEN
  C1092SPTG_PROD `&0 <= r * (c1092mcs_kE d t h r + abs(c1092mcs_deltaE d t h r))` THEN
  C1092SPTG_PROD `&0 <= r * c1092mcs_kE d t h r` THEN
  REWRITE_TAC[c1092sptg_H00; c1092sptg_H01; c1092sptg_H10; c1092sptg_H11] THEN
  REPEAT CONJ_TAC THEN C1092SPTG_LIN);;

(* common opening of the four modes: supports and side coefficients *)
let C1092SPTG_MODE_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092SPTG_V C1092SPTG_BOUNDARY_SUPPORTS) THEN
  MP_TAC(SPECL C1092SPTG_V C1092SPTG_CENTRAL_CAP) THEN
  MP_TAC(SPECL C1092SPTG_V C1092SPTG_RECIPIENT_CAP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spts_input] o
    check (can (term_match [] `c1092spts_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `sE:real`; `cB:real`; `sB:real`]
    C1092SPTG_SIDE_COEFFICIENTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter x y`) o concl)) THEN
  C1092PRS_NORMAL_TAC;;

let C1092SPTG_MODE_CLOSE_TAC hs =
  REWRITE_TAC(C1092SPTG_DEFS @ [c1092mcs_G00; c1092mcs_G01; c1092mcs_G10; c1092mcs_G11;
    c1092sptg_H00; c1092sptg_H01; c1092sptg_H10; c1092sptg_H11] @ hs) THEN
  REAL_ARITH_TAC;;

(* Lean: mode00 *)
let C1092SPTG_MODE00 = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB /\
     ABT_upper cB sB uB vB aB (--sC) cC <= vC /\
     ABT_upper cB sB uB vB aB cE sE <= uE
     ==> c1092mcs_G00 cC sC cE sE cB sB < &0`,
  C1092SPTG_MODE_OPEN_TAC THEN
  C1092SPTG_PROD_MP `&0 <= cE * (((&543 / &500) * sC - &1 - (aC - &1)) -
     (--sC * lcx cB sB uB vB aC - &2 * cC +
      (aC / &2) * (cC * (cB + sB) + c1092mcs_kC cC sC cB sB +
                   abs(c1092mcs_deltaC cC sC cB sB))))` THEN
  C1092SPTG_PROD_MP `&0 <= sC * ((cE - (&14 / &25) * sE - &1 - (aC - &1)) -
     (cE * lcx cB sB uB vB aC - &2 * sE +
      (aC / &2) * (sE * (cB + sB) + c1092mcs_kE cE sE cB sB +
                   abs(c1092mcs_deltaE cE sE cB sB))))` THEN
  C1092SPTG_PROD_MP `&0 < (aC - &1) * c1092sptg_H00 cC sC cE sE cB sB` THEN
  C1092SPTG_MODE_CLOSE_TAC []);;

(* Lean: mode01 *)
let C1092SPTG_MODE01 = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB /\
     ABT_upper cB sB uB vB aB (--sC) cC <= vC /\
     ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB
     ==> c1092mcs_G01 cC sC cE sE cB sB < &0`,
  C1092SPTG_MODE_OPEN_TAC THEN
  C1092SPTG_PROD_MP `&0 <= cB * (((&543 / &500) * sC - &1 - (aC - &1)) -
     (--sC * lcx cB sB uB vB aC - &2 * cC +
      (aC / &2) * (cC * (cB + sB) + c1092mcs_kC cC sC cB sB +
                   abs(c1092mcs_deltaC cC sC cB sB))))` THEN
  C1092SPTG_PROD_MP `&0 <= sC * ((c1092mcs_FE cE sE cB sB - (aC - &1) * c1092mcs_kE cE sE cB sB) -
     (cB * lcx cB sB uB vB aC - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)))` THEN
  C1092SPTG_PROD_MP `&0 < (aC - &1) * c1092sptg_H01 cC sC cE sE cB sB` THEN
  C1092SPTG_MODE_CLOSE_TAC []);;

(* Lean: mode10 *)
let C1092SPTG_MODE10 = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB /\
     ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB /\
     ABT_upper cB sB uB vB aB cE sE <= uE
     ==> c1092mcs_G10 cC sC cE sE cB sB < &0`,
  C1092SPTG_MODE_OPEN_TAC THEN
  C1092SPTG_PROD_MP `&0 <= cE * ((c1092mcs_FC cC sC cB sB - (aC - &1) *
        (c1092mcs_kC cC sC cB sB + abs(c1092mcs_deltaC cC sC cB sB))) -
     (--sB * lcx cB sB uB vB aC - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)))` THEN
  C1092SPTG_PROD_MP `&0 <= sB * ((cE - (&14 / &25) * sE - &1 - (aC - &1)) -
     (cE * lcx cB sB uB vB aC - &2 * sE +
      (aC / &2) * (sE * (cB + sB) + c1092mcs_kE cE sE cB sB +
                   abs(c1092mcs_deltaE cE sE cB sB))))` THEN
  C1092SPTG_PROD_MP `&0 < (aC - &1) * c1092sptg_H10 cC sC cE sE cB sB` THEN
  C1092SPTG_MODE_CLOSE_TAC []);;

(* Lean: mode11 *)
let C1092SPTG_MODE11 = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB /\
     ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB /\
     ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB
     ==> c1092mcs_G11 cC sC cE sE cB sB < &0`,
  C1092SPTG_MODE_OPEN_TAC THEN
  C1092SPTG_PROD_MP `&0 <= cB * ((c1092mcs_FC cC sC cB sB - (aC - &1) *
        (c1092mcs_kC cC sC cB sB + abs(c1092mcs_deltaC cC sC cB sB))) -
     (--sB * lcx cB sB uB vB aC - &2 * cB + (aC / &2) * (cB * (cB + sB) + &1)))` THEN
  C1092SPTG_PROD_MP `&0 <= sB * ((c1092mcs_FE cE sE cB sB - (aC - &1) * c1092mcs_kE cE sE cB sB) -
     (cB * lcx cB sB uB vB aC - &2 * sB + (aC / &2) * (sB * (cB + sB) + &1)))` THEN
  C1092SPTG_PROD_MP `&0 < (aC - &1) * c1092sptg_H11 cC sC cE sE cB sB` THEN
  SUBGOAL_THEN `(&2 - aC * (cB + sB) / &2) * (cB * cB + sB * sB) =
                &2 - aC * (cB + sB) / &2` MP_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  C1092SPTG_MODE_CLOSE_TAC []);;

(* Lean: one_mode_negative_quarter *)
let C1092SPTG_ONE_MODE_NEGATIVE_QUARTER = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB
     ==> c1092mcs_G00 cC sC cE sE cB sB < &0 \/ c1092mcs_G01 cC sC cE sE cB sB < &0 \/
         c1092mcs_G10 cC sC cE sE cB sB < &0 \/ c1092mcs_G11 cC sC cE sE cB sB < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092SPTG_V C1092SPTS_CENTRAL_SOURCES) THEN
  MP_TAC(SPECL C1092SPTG_V C1092SPTS_RECIPIENT_SOURCES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
  ASM_SIMP_TAC[SPECL C1092SPTG_V C1092SPTG_MODE00; SPECL C1092SPTG_V C1092SPTG_MODE01;
               SPECL C1092SPTG_V C1092SPTG_MODE10; SPECL C1092SPTG_V C1092SPTG_MODE11]);;

(* Lean: one_mode_negative *)
let C1092SPTG_ONE_MODE_NEGATIVE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB
     ==> exists cQ sQ uQ vQ aQ.
           cQ * cQ + sQ * sQ = &1 /\ &0 < aQ /\ aQ = aB /\
           (forall x y. linside cQ sQ uQ vQ aQ x y <=> linside cB sB uB vB aB x y) /\
           c1092mcs_quarter cQ sQ /\
           (c1092mcs_G00 cC sC cE sE cQ sQ < &0 \/ c1092mcs_G01 cC sC cE sE cQ sQ < &0 \/
            c1092mcs_G10 cC sC cE sE cQ sQ < &0 \/ c1092mcs_G11 cC sC cE sE cQ sQ < &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    WCB_EXISTS_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cQ:real` (X_CHOOSE_THEN `sQ:real` (X_CHOOSE_THEN `uQ:real`
    (X_CHOOSE_THEN `vQ:real` (X_CHOOSE_THEN `aQ:real` STRIP_ASSUME_TAC))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aQ:real = aB`)) THEN
  MAP_EVERY EXISTS_TAC [`cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aB:real`] THEN
  SUBGOAL_THEN `c1092mcs_quarter cQ sQ` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[c1092mcs_quarter; REAL_POW_2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SPECL (C1092SPTG_V @ []) C1092SPTG_ONE_MODE_NEGATIVE_QUARTER |>
    INST [`cQ:real`,`cB:real`; `sQ:real`,`sB:real`; `uQ:real`,`uB:real`;
          `vQ:real`,`vB:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB` THEN
  ASM_REWRITE_TAC[c1092spts_input; ldisj]);;

(* Lean: ModesNonnegative (definition) *)
let c1092sptg_modesNonnegative = new_definition
 `c1092sptg_modesNonnegative (c:real) s d t <=>
    forall h r. c1092mcs_quarter h r
          ==> &0 <= c1092mcs_G00 c s d t h r /\ &0 <= c1092mcs_G01 c s d t h r /\
              &0 <= c1092mcs_G10 c s d t h r /\ &0 <= c1092mcs_G11 c s d t h r`;;

(* Lean: impossible_of_modes *)
let C1092SPTG_IMPOSSIBLE_OF_MODES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092sptg_modesNonnegative cC sC cE sE
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092sptg_modesNonnegative] THEN STRIP_TAC THEN
  MP_TAC(SPECL C1092SPTG_V C1092SPTG_ONE_MODE_NEGATIVE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`cQ:real`; `sQ:real`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> try fst(dest_const t) = "c1092mcs_G00" with _ -> false))
          (concl th))) THEN
  ASM_REWRITE_TAC[GSYM REAL_NOT_LT]);;

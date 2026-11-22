(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMPositiveBoundaryOrigin.lean           *)
(* (N12Compact.C1092MPPMPositiveBoundaryOrigin), POSITIVE-BOUNDARY-ORIGIN    *)
(* Theorem 1.  Squares C = cC sC uC vC aC (central), B = cB sB uB vB aB      *)
(* (boundary).  Normal is c977cc_normal; scalars C1092PBO_* / c1092pbo_*;    *)
(* support formulas C1092WS_*; upper_neg/lower_neg C1092MCSUP_NEGATIVE_      *)
(* SUPPORT; vertex / strict_closed_segment OCWPVG_*; square_support_bound    *)
(* C1092MPWS_SQUARE_SUPPORT_BOUND; SAT step ABT_FOUR_AXES.                   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveBoundaryOriginScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_C1092_MMMP_PhysicalWallSupport.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;

let C1092PBOT_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092PBOT_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092PBOT_LP_TAC; ALL_TAC];;

let C1092PBOT_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
                  FIRST [REAL_ARITH_TAC; C1092PBOT_LP_TAC]; DISCH_TAC];;

let C1092PBOT_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: Input (structure) *)
let c1092pbot_input = new_definition
 `c1092pbot_input cC sC uC vC aC cB sB uB vB aB <=>
    &1 < aC /\ aC = aB /\ c977cc_normal cC sC /\ c977cc_normal cB sB /\
    --cC - sC / &2 <= uC /\ uC + aC <= &0 /\ vC + aC <= sC /\
    linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
    linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
    linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
    linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
    linside cB sB uB vB aB (--(&13 / &50)) (--(&1)) /\
    (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
    (forall y. --(&543 / &500) <= y ==> y <= --(&1) ==> ~linside cB sB uB vB aB (--(&1)) y) /\
    ldisj cC sC uC vC aC cB sB uB vB aB`;;

let C1092PBOT_SETUP_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pbot_input] o
    check (fun th -> can (term_match [] `c1092pbot_input a b c d e f g h i j`) (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C1092PBOT_NORMAL_TAC;;

let C1092PBOT_HYPS =
  `cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
   c1092pbot_input cC sC uC vC aC cB sB uB vB aB`;;

(* Lean: lower_wall (private) *)
let C1092PBOT_LOWER_WALL = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c977cc_normal c s /\
               (forall x y. linside c s u v a x y ==> --(&2) <= y)
               ==> --(&2) <= s * u + c * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PBOT_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&0`; `--(&1)`; `&2`]
    C1092MPWS_SQUARE_SUPPORT_BOUND) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`x:real`; `y:real`]) THEN ASM_REWRITE_TAC[] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx; lcy; tss_support_radius] THEN
  SUBGOAL_THEN `abs(&0 * c + --(&1) * s) = s /\ abs(--(&0) * s + --(&1) * c) = c`
  (fun th -> REWRITE_TAC[th]) THENL [CONJ_TAC THEN RASM_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: missing_upper (private) *)
let C1092PBOT_MISSING_UPPER = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092pbot_input cC sC uC vC aC cB sB uB vB aB /\
     ~linside cB sB uB vB aB (&0) (--(&1))
     ==> uB + aB <= --sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PBOT_SETUP_TAC THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside cB sB uB vB aC (&0) (--(&1))` THEN REWRITE_TAC[linside] THEN
  C1092PBOT_LP_TAC);;

(* Lean: direct_origin *)
let C1092PBOT_DIRECT_ORIGIN = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092pbot_input cC sC uC vC aC cB sB uB vB aB /\ &457 / &500 <= aB * cB
     ==> linside cB sB uB vB aB (&0) (--(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  C1092PBOT_USE C1092PBOT_MISSING_UPPER
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  C1092PBOT_SETUP_TAC THEN
  C1092PBOT_USE C1092PBOT_LOWER_WALL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `uB:real`; `vB + aC:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                           else REWRITE_RULE[linside] th) THEN
  ASM_CASES_TAC `sB = &0` THENL [C1092PBOT_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sB` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `x = cB * uB - sB * (vB + aC)` THEN
  ABBREV_TAC `y = sB * uB + cB * (vB + aC)` THEN
  SUBGOAL_THEN `aC * cB - &2 <= y /\ --(&543 / &500) <= y` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "y" THEN C1092PBOT_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cB * x = uB - sB * y /\ --sB * x + cB * y = vB + aC` STRIP_ASSUME_TAC THENL
  [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN UNDISCH_TAC `cB * cB + sB * sB = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092PBOT_PROD `&0 <= sB * (y - (aC * cB - &2))` THEN
  C1092PBOT_PROD `&0 < cB * sB` THEN
  C1092PBOT_PROD `&0 < (aC - &1) * (&1 + cB * sB)` THEN
  C1092PBOT_PROD `&0 <= (&1 - cB) * (&1 - sB)` THEN
  SUBGOAL_THEN `x < --(&1)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PBOT_PROD `&0 <= cB * (x + &1)` THEN C1092PBOT_LP_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `--(&1) <= y` THENL
  [FIRST_X_ASSUM(MP_TAC o SPEC `--(&1)` o check (fun th -> is_forall(concl th) &&
     can (find_term ((=) `--(&543 / &500)`)) (concl th))) THEN
   MATCH_MP_TAC(TAUT `a /\ b /\ c ==> (a ==> b ==> ~c) ==> false`) THEN REWRITE_TAC[linside] THEN
   C1092PBOT_PROD `&0 < sB * (--(&1) - x)` THEN
   C1092PBOT_PROD `&0 <= cB * (y + &1)` THEN
   C1092PBOT_LP_TAC;
   ALL_TAC] THEN
  ABBREV_TAC `t = (--(&1) - x) / (--(&2 / &5) - x)` THEN
  SUBGOAL_THEN `&0 < --(&2 / &5) - x` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * (--(&2 / &5) - x) = --(&1) - x /\ &0 < t /\ t < &1`
  STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "t" THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    MATCH_MP_TAC REAL_LT_DIV THEN RASM_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `x:real`; `y:real`;
                `--(&2 / &5)`; `--(&1)`; `t:real`] OCWPVG_STRICT_CLOSED_SEGMENT) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `lclosed cB sB uB vB aC x y` (fun th -> REWRITE_TAC[th]) THENL
   [MAP_EVERY EXPAND_TAC ["x"; "y"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   ASM_REWRITE_TAC[linside]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) * x + t * --(&2 / &5) = --(&1)` SUBST1_TAC THENL
  [UNDISCH_TAC `t * (--(&2 / &5) - x) = --(&1) - x` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - t) * y + t * --(&1)` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `--(&543 / &500)`)) (concl th))) THEN
  C1092PBOT_PROD `&0 <= (&1 - t) * (y + &543 / &500)` THEN
  C1092PBOT_PROD `&0 <= (&1 - t) * (--(&1) - y)` THEN
  MATCH_MP_TAC(TAUT `a /\ b ==> (a ==> b ==> ~c) ==> c ==> false`) THEN
  C1092PBOT_LP_TAC);;

(* Lean: boundary_data (private) *)
let C1092PBOT_BOUNDARY_DATA = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092pbot_input cC sC uC vC aC cB sB uB vB aB /\
     ~linside cB sB uB vB aB (&0) (--(&1))
     ==> &0 < sB /\ (&5 / &12) * cB < sB /\ uB + aB <= --sB /\
         aB * (cB + sB) - &2 + sB pow 2 <= cB * (vB + aB)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1092PBOT_USE C1092PBOT_MISSING_UPPER
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  SUBGOAL_THEN `aB * cB < &457 / &500` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
     C1092PBOT_DIRECT_ORIGIN) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  C1092PBOT_SETUP_TAC THEN
  C1092PBOT_USE C1092PBOT_LOWER_WALL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] THEN
  C1092PBOT_PROD `&0 < (aC - &1) * cB` THEN
  SUBGOAL_THEN `cB < &457 / &500` ASSUME_TAC THENL [C1092PBOT_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&5 / &12) * cB < sB` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C1092PBOT_PROD `&0 <= (&5 * cB - &12 * sB) * (&5 * cB + &12 * sB)` THEN
   C1092PBOT_PROD `&0 < (&457 / &500 - cB) * (&457 / &500 + cB)` THEN
   C1092PBOT_LP_TAC; ALL_TAC] THEN
  C1092PBOT_PROD `&0 <= sB * (--sB - (uB + aC))` THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN C1092PBOT_LP_TAC);;

(* Lean: cone (private) *)
let C1092PBOT_CONE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092pbot_input cC sC uC vC aC cB sB uB vB aB /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cB sB uB vB aB nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < ny /\ nx < (&30 / &37) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PBOT_SETUP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`;
                `--(&13 / &50)`; `--(&1)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `--(&13 / &50)`; `&0`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `--(&1)`; `--(&2 / &5)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092PBOT_LP_TAC);;

(* the reversed cone (upper_neg / lower_neg step of separators) *)
let C1092PBOT_CONE_REV = prove
 (`forall cC sC uC vC aC cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092pbot_input cC sC uC vC aC cB sB uB vB aB /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cB sB uB vB aB nx ny
     ==> &0 < --ny /\ --nx < (&30 / &37) * --ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092PBOT_CONE THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[C1092MCSUP_NEGATIVE_SUPPORT] THEN
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REAL_ARITH_TAC);;

(* Lean: separators (private) *)
let C1092PBOT_SEPARATORS = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092pbot_input cC sC uC vC aC cB sB uB vB aB
     ==> ABT_upper cB sB uB vB aB (--sC) cC <= vC \/
         vB + aB <= ABT_lower cC sC uC vC aC (--sB) cB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ASSUME `c1092pbot_input cC sC uC vC aC cB sB uB vB aB`) THEN
  REWRITE_TAC[c1092pbot_input] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C1092PBOT_NORMAL_TAC THEN
  let use th nx ny =
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; nx; ny] th) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     RASM_ARITH_TAC;
     RASM_ARITH_TAC] in
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ldisj cC sC uC vC aC cB sB uB vB aC` THEN
   REWRITE_TAC[ldisj] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC;
         use C1092PBOT_CONE `cB:real` `sB:real`;
         use C1092PBOT_CONE_REV `cB:real` `sB:real`;
         use C1092PBOT_CONE_REV `--sB:real` `cB:real`;
         use C1092PBOT_CONE `cC:real` `sC:real`;
         use C1092PBOT_CONE_REV `cC:real` `sC:real`;
         use C1092PBOT_CONE_REV `--sC:real` `cC:real`]);;

(* substitute proved values of max/min terms into the other assumptions *)
let C1092PBOT_MM_TAC =
  ASSUM_LIST(fun ths ->
    let mm th = is_eq(concl th) &&
      (let l = lhand(concl th) in is_comb l &&
        (let f,_ = strip_comb l in f = `max:real->real->real` || f = `min:real->real->real`)) in
    let eqs = filter mm ths in
    RULE_ASSUM_TAC(fun th -> if mm th then th else REWRITE_RULE eqs th));;

(* Lean: origin *)
let C1092PBOT_ORIGIN = prove
 (`forall cC sC uC vC aC cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092pbot_input cC sC uC vC aC cB sB uB vB aB
     ==> linside cB sB uB vB aB (&0) (--(&1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  C1092PBOT_USE C1092PBOT_BOUNDARY_DATA
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  C1092PBOT_USE C1092PBOT_SEPARATORS
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
     `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  C1092PBOT_SETUP_TAC THEN
  C1092PBOT_USE C1092PBOT_LOWER_WALL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`] THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) || is_forall(concl th) then th
                           else REWRITE_RULE[linside] th) THEN
  C1092PBOT_PROD `&0 < cC * cB` THEN C1092PBOT_PROD `&0 <= sC * sB` THEN
  SUBGOAL_THEN `&0 < cC * cB + sC * sB` ASSUME_TAC THENL [C1092PBOT_LP_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [(* the central separator *)
   MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `--sC:real`; `cC:real`]
     C1092WS_FORMULAS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT2 th) THEN
     ASSUME_TAC(AP_TERM `(*) (cB:real)` (CONJUNCT2 th))) THEN
   SUBGOAL_THEN `max (-- --sC * sB + cC * cB) (&0) = -- --sC * sB + cC * cB /\
                 max (--sC * cB + cC * sB) (&0) =
                   (cC * sB - sC * cB) + max (--(cC * sB - sC * cB)) (&0) /\
                 &0 <= max (--(cC * sB - sC * cB)) (&0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < cC * cB + sC * sB` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   C1092PBOT_MM_TAC THEN
   C1092PBOT_USE C1092PBO_V_POSITIVE [`cC:real`; `sC:real`; `cB:real`; `sB:real`] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[c1092pbo_vMargin]) THEN
   C1092PBOT_PROD `&0 <= (cC * cB + sC * sB) *
                         (sB * (uB + aC) + cB * (vB + aC) - aC * (cB + sB) + &2)` THEN
   C1092PBOT_PROD `&0 <= sC * (--(uB + aC) - sB)` THEN
   C1092PBOT_PROD `&0 <= cB * (sC - aC - vC)` THEN
   C1092PBOT_PROD `&0 <= (cC * cB + sC * sB) * (cB + sB)` THEN
   C1092PBOT_PROD `&0 <= cB * max (--(cC * sB - sC * cB)) (&0)` THEN
   C1092PBOT_PROD `&0 <= (aC - &1) * (cB + (cC * cB + sC * sB) * (cB + sB) +
                                       cB * max (--(cC * sB - sC * cB)) (&0))` THEN
   C1092PBOT_PROD `&0 <= cB * (vC - ABT_upper cB sB uB vB aC (--sC) cC)` THEN
   SUBGOAL_THEN `sC * (uB + aC) * (cB * cB + sB * sB) = sC * (uB + aC)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
   C1092PBOT_LP_TAC;
   (* the boundary separator *)
   MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sB:real`; `cB:real`]
     C1092WS_FORMULAS) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN
     ASSUME_TAC(AP_TERM `(*) (cB:real)` (CONJUNCT1 th))) THEN
   SUBGOAL_THEN `min (-- --sB * sC + cB * cC) (&0) = &0` ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < cC * cB + sC * sB` THEN REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `cB * sB * (cC * cC + sC * sC) = cB * sB` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
   C1092PBOT_PROD `&0 <= cB * (ABT_lower cC sC uC vC aC (--sB) cB - (vB + aC))` THEN
   C1092PBOT_PROD `&0 <= cB * (cC * cB + sC * sB) * (sC - aC - vC)` THEN
   ASM_CASES_TAC `&0 <= cC * sB - sC * cB` THENL
   [SUBGOAL_THEN `min (--sB * cC + cB * sC) (&0) = --sB * cC + cB * sC` ASSUME_TAC THENL
    [UNDISCH_TAC `&0 <= cC * sB - sC * cB` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092PBOT_MM_TAC THEN
    C1092PBOT_USE C1092PBO_PLUS_POSITIVE [`cC:real`; `sC:real`; `cB:real`; `sB:real`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092pbo_plusMargin; c1092pbo_plusPhi]) THEN
    C1092PBOT_PROD `&0 <= cB * (cC * sB - sC * cB) * ((uC + aC) - (aC - cC - sC / &2))` THEN
    C1092PBOT_PROD `&0 <= cB * ((cC * cB + sC * sB) + (cC * sB - sC * cB))` THEN
    C1092PBOT_PROD `&0 <= (aC - &1) * (cB + sB + cB * ((cC * cB + sC * sB) + (cC * sB - sC * cB)))` THEN
    C1092PBOT_LP_TAC;
    SUBGOAL_THEN `min (--sB * cC + cB * sC) (&0) = &0` ASSUME_TAC THENL
    [UNDISCH_TAC `~(&0 <= cC * sB - sC * cB)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    C1092PBOT_MM_TAC THEN
    SUBGOAL_THEN `cC * sB - sC * cB <= &0` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
    C1092PBOT_USE C1092PBO_MINUS_POSITIVE [`cC:real`; `sC:real`; `cB:real`; `sB:real`] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[c1092pbo_minusMargin; c1092pbo_minusPhi]) THEN
    C1092PBOT_PROD `&0 <= cB * --(cC * sB - sC * cB) * (--aC - uC)` THEN
    C1092PBOT_PROD `&0 <= cB * ((cC * cB + sC * sB) - (cC * sB - sC * cB))` THEN
    C1092PBOT_PROD `&0 <= (aC - &1) * (cB + sB + cB * ((cC * cB + sC * sB) - (cC * sB - sC * cB)))` THEN
    C1092PBOT_LP_TAC]]);;

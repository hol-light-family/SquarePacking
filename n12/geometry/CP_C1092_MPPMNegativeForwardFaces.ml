(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeForwardFaces.lean             *)
(* (N12Compact.C1092MPPMNegativeForward), NEGATIVE-FORWARD-POSITIVE-H        *)
(* sections 2--4.  Squares C = cC sC uC vC aC, E = cE sE uE vE aE and the     *)
(* bar square B = cB sB uB vB aB.  Normal is c977cc_normal; scalars          *)
(* C1092NFS_*; WallProfile.vertex is OCWPVG_VERTEX; ClosedPointExclusion is  *)
(* LCLOSED_SEGMENT / OUTSIDE_OF_CLOSED (p2_base); centerY is lcy.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeForwardScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let C1092NFF_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* the goal F, from an excluded point ~linside q x y (an assumption) *)
let C1092NFF_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside] THEN C1092NFF_LP_TAC;;

(* the goal F, from ldisj q r and a strict point of r at (x,y) *)
let C1092NFF_APART_TAC dtm x y =
  UNDISCH_TAC dtm THEN REWRITE_TAC[ldisj] THEN
  DISCH_THEN(MP_TAC o SPECL [x; y]) THEN ASM_REWRITE_TAC[linside] THEN C1092NFF_LP_TAC;;

(* Lean: Input (structure) *)
let c1092nff_input = new_definition
 `c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB <=>
    &1 < aC /\ aC = aE /\ c977cc_normal cC (--sC) /\ c977cc_normal cE sE /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
    linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
    ~linside cC sC uC vC aC (--(&1)) (&0) /\
    ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
    (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
    ldisj cC sC uC vC aC cE sE uE vE aE /\
    ldisj cC sC uC vC aC cB sB uB vB aB`;;

(* Lean: SourceProfile (structure) *)
let c1092nff_sourceProfile = new_definition
 `c1092nff_sourceProfile cC sC uC vC aC <=>
    &0 < --sC /\ &87 / &100 < cC /\ --sC < &49 / &100 /\ cC < &1 /\
    --cC <= uC /\ uC + aC <= --(&13 / &50) * sC /\
    vC + aC <= (&7 / &20) * (cC + sC) /\ --cC + (&14 / &25) * sC <= vC`;;

let C1092NFF_SETUP_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092nff_input] o
    check (fun th -> can (term_match [] `c1092nff_input a b c d e f g h i j k l m n o'`)
                         (concl th))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th);;

let C1092NFF_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: source_profile *)
let C1092NFF_SOURCE_PROFILE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB
     ==> c1092nff_sourceProfile cC sC uC vC aC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NFF_SETUP_TAC THEN C1092NFF_NORMAL_TAC THEN
  SUBGOAL_THEN `--cC <= uC` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092NFF_MISS_TAC `~linside cC sC uC vC aC (--(&1)) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `uC + aC <= --(&13 / &50) * sC` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092NFF_APART_TAC `ldisj cC sC uC vC aC cE sE uE vE aC` `&0` `--(&13 / &50)`; ALL_TAC] THEN
  SUBGOAL_THEN `vC + aC <= (&7 / &20) * (cC + sC)` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   C1092NFF_MISS_TAC `~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC:real`] C1092NFS_SOURCE_ANGLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092NFF_LP_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `--cC + (&14 / &25) * sC <= vC` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_ASSUM(MP_TAC o SPEC `--(&14 / &25)` o check (is_forall o concl)) THEN CONV_TAC(LAND_CONV REAL_RAT_REDUCE_CONV) THEN
   REWRITE_TAC[] THEN DISCH_TAC THEN
   C1092NFF_APART_TAC `ldisj cC sC uC vC aC cB sB uB vB aB` `--(&14 / &25)` `--(&1)`;
   ALL_TAC] THEN
  ASM_REWRITE_TAC[c1092nff_sourceProfile]);;

(* Lean: above_bar (private) *)
let C1092NFF_ABOVE_BAR = prove
 (`forall cC sC uC vC aC cB sB uB vB aB X Y.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     lclosed cC sC uC vC aC X Y /\ linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
     --(&14 / &25) <= X /\ X <= &0 /\
     (forall x. --(&14 / &25) <= x ==> x <= &0 ==> linside cB sB uB vB aB x (--(&1))) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> --(&1) < Y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `t = (--(&1) - Y) / --Y` THEN
  SUBGOAL_THEN `&0 < --Y` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `t * --Y = --(&1) - Y` ASSUME_TAC THENL
  [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t /\ t <= &1` STRIP_ASSUME_TAC THENL
  [EXPAND_TAC "t" THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN RASM_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN RASM_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `X:real`; `Y:real`;
                `--(&13 / &50)`; `&0`; `t:real`] LCLOSED_SEGMENT) THEN
  ANTS_TAC THENL
  [ASM_SIMP_TAC[LINSIDE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - t) * Y + t * &0 = --(&1)` SUBST1_TAC THENL
  [UNDISCH_TAC `t * --Y = --(&1) - Y` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `(&1 - t) * X + t * --(&13 / &50)`; `--(&1)`] OUTSIDE_OF_CLOSED) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `ldisj cC sC uC vC aC cB sB uB vB aB` THEN
   REWRITE_TAC[ldisj] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `p ==> (~p ==> false)`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - t) * X + t * --(&13 / &50)` o
    check (is_forall o concl)) THEN
  MATCH_MP_TAC(TAUT `a /\ b ==> (a ==> b ==> c) ==> c`) THEN
  SUBGOAL_THEN `&0 <= (&1 - t) * (X + &14 / &25) /\ &0 <= (&1 - t) * --X`
  STRIP_ASSUME_TAC THENL
  [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN C1092NFF_LP_TAC);;

(* Lean: center_floor *)
let C1092NFF_CENTER_FLOOR = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092nff_sourceProfile cC sC uC vC aC
     ==> --(&1) + aC * (cC - sC) / &2 < lcy cC sC uC vC aC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NFF_SETUP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092nff_sourceProfile] o
    check (fun th -> can (term_match [] `c1092nff_sourceProfile a b c d e`) (concl th))) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `uC + aC:real`; `vC:real`]
    OCWPVG_VERTEX) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= cC * (uC - --cC) /\ &0 <= --sC * (vC - (--cC + (&14 / &25) * sC)) /\
                &0 < cC * (aC - &1) /\
                &0 < (&1 + sC) * (cC - (&11 / &25) * (&1 - sC))` STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN
   (MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `--(&14 / &25) < cC * (uC + aC) - sC * vC` ASSUME_TAC THENL
  [C1092NFF_LP_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&1) < sC * (uC + aC) + cC * vC` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `cC * (cC * (uC + aC) - sC * vC) + sC * (sC * (uC + aC) + cC * vC) = uC + aC`
   ASSUME_TAC THENL
   [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= --sC * (--(&1) - (sC * (uC + aC) + cC * vC))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `cC * (cC * (uC + aC) - sC * vC) <= &0` ASSUME_TAC THENL
   [C1092NFF_LP_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `cC * (uC + aC) - sC * vC <= &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < cC * (cC * (uC + aC) - sC * vC)` MP_TAC THENL
    [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
   MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                 `cC * (uC + aC) - sC * vC`; `sC * (uC + aC) + cC * vC`] C1092NFF_ABOVE_BAR) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[linside] THEN RASM_ARITH_TAC; RASM_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[lcy] THEN RASM_ARITH_TAC);;

(* Lean: target_lower *)
let C1092NFF_TARGET_LOWER = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092nff_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     ~linside cE sE uE vE aE (&1 / &2) (--(&1))
     ==> --cE - sE / &2 <= vE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092NFF_SETUP_TAC THEN C1092NFF_NORMAL_TAC THEN
  SUBGOAL_THEN `cE / &2 - sE < uE + aC` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&13 * sE < &3 * cE` ASSUME_TAC THENL [C1092NFF_LP_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `--(&7 / &20) * (cE + sE) <= uE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aC` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`--(&7 / &20)`; `--(&7 / &20)`]) THEN
    ASM_REWRITE_TAC[linside] THEN C1092NFF_LP_TAC; ALL_TAC] THEN
   C1092NFF_LP_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  C1092NFF_MISS_TAC `~linside cE sE uE vE aC (&1 / &2) (--(&1))`);;

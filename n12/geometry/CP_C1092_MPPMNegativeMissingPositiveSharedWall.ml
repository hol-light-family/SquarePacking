(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMNegativeMissingPositiveSharedWall    *)
(* .lean (N12Compact.C1092MPPMNegativeMissingPositiveSharedWall).            *)
(* NEGATIVE-MISSING-POSITIVE-SHARED-WALL Theorem 1.  Squares C, L are       *)
(* cC sC uC vC aC and cL sL uL vL aL; Data C is c1092nmpsw_data; Normal:     *)
(* c977cc_normal; Quarter: c1092mcs_quarter; upper / lower: ABT_upper /      *)
(* ABT_lower; upper_np / upper_pos_pos: C1092WS_UPPER_NP /                   *)
(* C1092TFSU_UPPER_POS_POS; strict_bounds: ABT_STRICT_BOUNDS; ownV: ABT_OWNV; *)
(* left_center / width_bounds / left_face / FaceNormal / width0:             *)
(* C1092SBS_LEFT_CENTER / C1092SBS_WIDTH_BOUNDS / C1092SBS_LEFT_FACE /       *)
(* c1092sbs_FaceNormal / c1092sbs_width0; directed_faces:                    *)
(* C1092MPBEB_DIRECTED_FACES; Scalars: c1092nmps_F0 .. B2 and                *)
(* C1092NMPS_CENTRAL_POSITIVE / NORTHWEST_BEFORE / NORTHWEST_AFTER;          *)
(* leftValue: c1092mpbes_leftValue.  Tag C1092NMPSW_.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMNegativeMissingPositiveSharedWallScalars.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundEnvelopesBottom.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_ShallowBoundarySupport.ml";;

(* Lean: Data (structure) *)
let c1092nmpsw_data = new_definition
 `c1092nmpsw_data (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    c977cc_normal c s /\ &0 < s /\ s / (&1 + c) <= &3 / &10 /\
    linside c s u v a (--(&1)) (--(&13 / &50)) /\
    linside c s u v a (--(&1 / &2)) (&0) /\
    --c - s <= u /\ u + a <= &0 /\ (&14 / &25) * s - c <= v`;;

let C1092NMPSW_LIN = NLIN_TAC ~deg2:false [];;

let C1092NMPSW_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092NMPSW_LIN; ALL_TAC];;

(* Lean: northwest (private) *)
let C1092NMPSW_NORTHWEST = prove
 (`forall c s u v a h r.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092nmpsw_data c s u v a /\ c1092mcs_quarter h r
     ==> &2 * h + r / &5 - (a / &2) * (&1 + h pow 2 + h * r) < ABT_upper c s u v a (--h) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092nmpsw_data] (ASSUME `c1092nmpsw_data c s u v a`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal c s`) o concl)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] (ASSUME `c977cc_normal c s`)) THEN
  MP_TAC(ASSUME `c1092mcs_quarter h r`) THEN REWRITE_TAC[c1092mcs_quarter] THEN STRIP_TAC THEN
  MP_TAC(SPEC `r:real` REAL_LE_POW_2) THEN MP_TAC(SPEC `h:real` REAL_LE_POW_2) THEN
  REPEAT DISCH_TAC THEN
  ABBREV_TAC `lam = --c * h + s * r` THEN ABBREV_TAC `kap = c * r + s * h` THEN
  C1092NMPSW_PROD `&0 <= h * r` THEN
  SUBGOAL_THEN `&1 <= h + r` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC [SQ_NONNEG `h + r - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < kap` ASSUME_TAC THENL
   [C1092NMPSW_PROD `&0 <= (c - s) * r` THEN C1092NMPSW_PROD `&0 <= s * (h + r - &1)` THEN
    EXPAND_TAC "kap" THEN C1092NMPSW_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `--h * c + r * s = lam /\ -- --h * s + r * c = kap` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["lam"; "kap"] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `lam <= &0` THENL
   [MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--h`; `r:real`; `lam:real`; `kap:real`]
      C1092WS_UPPER_NP) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
    C1092NMPSW_PROD `&0 <= --lam * --(u + a)` THEN
    C1092NMPSW_PROD `&0 <= kap * (v - ((&14 / &25) * s - c))` THEN
    C1092NMPSW_PROD `&0 < (a - &1) * (kap - lam + (&1 + h pow 2 + h * r) / &2)` THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NMPS_NORTHWEST_BEFORE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `kap - lam + (&1 + h pow 2 + h * r) / &2 + kap * ((&14 / &25) * s - c) - &2 * h - r / &5 =
                  c1092mpbes_leftValue (&1) (c1092nmps_A1 c s) (c1092nmps_B1 c s) h r`
      ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["lam"; "kap"] THEN
      REWRITE_TAC[c1092mpbes_leftValue; c1092nmps_A1; c1092nmps_B1] THEN
      UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092NMPSW_LIN;
    SUBGOAL_THEN `&0 <= lam` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `--h`; `r:real`; `lam:real`; `kap:real`]
      C1092TFSU_UPPER_POS_POS) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN DISCH_THEN SUBST1_TAC THEN
    C1092NMPSW_PROD `&0 <= lam * (u - (--c - s))` THEN
    C1092NMPSW_PROD `&0 <= kap * (v - ((&14 / &25) * s - c))` THEN
    C1092NMPSW_PROD `&0 < (a - &1) * (lam + kap + (&1 + h pow 2 + h * r) / &2)` THEN
    MP_TAC(SPECL [`c:real`; `s:real`; `h:real`; `r:real`] C1092NMPS_NORTHWEST_AFTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "lam" THEN UNDISCH_TAC `&0 <= lam` THEN
      EXPAND_TAC "lam" THEN REAL_ARITH_TAC; DISCH_TAC] THEN
    SUBGOAL_THEN `lam + kap + (&1 + h pow 2 + h * r) / &2 - lam * (c + s) +
                  kap * ((&14 / &25) * s - c) - &2 * h - r / &5 =
                  c1092mpbes_leftValue (&1) (c1092nmps_A2 c s) (c1092nmps_B2 c s) h r`
      ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["lam"; "kap"] THEN
      REWRITE_TAC[c1092mpbes_leftValue; c1092nmps_A2; c1092nmps_B2] THEN
      UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092NMPSW_LIN]);;

let C1092NMPSW_C = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092NMPSW_L = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`];;

(* Lean: cone (local of left_order) *)
let C1092NMPSW_CONE = prove
 (`forall cC sC uC vC aC cL sL uL vL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\
     c1092nmpsw_data cC sC uC vC aC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\ linside cL sL uL vL aC (--(&1)) (&0) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny
     ==> nx < &0 /\ &0 < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092nmpsw_data] (ASSUME `c1092nmpsw_data cC sC uC vC aC`)) THEN
  MP_TAC(SPECL (C1092NMPSW_C @ [`--(&1)`; `--(&13 / &50)`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092NMPSW_C @ [`--(&1 / &2)`; `&0`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092NMPSW_L @ [`--(&1)`; `&0`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL (C1092NMPSW_L @ [`--(&543 / &500)`; `&0`; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: central (local of left_order) *)
let C1092NMPSW_CENTRAL = prove
 (`forall cC sC uC vC aC cL sL uL vL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     c1092nmpsw_data cC sC uC vC aC /\
     (forall x y. linside cL sL uL vL aC x y ==> --(&2) <= x) /\
     lcy cL sL uL vL aC <= &1 / &5
     ==> ~(ABT_upper cC sC uC vC aC (--sC) cC <= ABT_lower cL sL uL vL aC (--sC) cC)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092nmpsw_data] (ASSUME `c1092nmpsw_data cC sC uC vC aC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal c s`) o concl)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`] C1092SBS_LEFT_CENTER) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`; `cC:real`; `sC:real`]
    C1092SBS_WIDTH_BOUNDS) THEN
  MP_TAC(SPECL C1092NMPSW_C ABT_OWNV) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092NMPS_CENTRAL_POSITIVE) THEN
  ASM_REWRITE_TAC[REAL_ARITH `-- &2 = --(&2)`] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `ABT_upper cC sC uC vC aC (--sC) cC <= ABT_lower cL sL uL vL aC (--sC) cC` THEN
  ASM_REWRITE_TAC[ABT_lower] THEN DISCH_TAC THEN
  C1092NMPSW_PROD `&0 <= sC * (lcx cL sL uL vL aC - (--(&2) + aC * c1092sbs_width0 cL sL / &2))` THEN
  C1092NMPSW_PROD `&0 <= cC * (&1 / &5 - lcy cL sL uL vL aC)` THEN
  C1092NMPSW_PROD `&0 <= sC * (cC + sC)` THEN
  C1092NMPSW_PROD `&0 < (aC - &1) * (&3 / &2 + sC * (cC + sC) / &2)` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092nmps_F0]) THEN
  C1092NMPSW_LIN);;

(* Lean: boundary (local of left_order) *)
let C1092NMPSW_BOUNDARY = prove
 (`forall cC sC uC vC aC cL sL uL vL nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &1 < aC /\
     c1092nmpsw_data cC sC uC vC aC /\
     linside cL sL uL vL aC (--(&543 / &500)) (&0) /\ linside cL sL uL vL aC (--(&1)) (&0) /\
     (forall x y. linside cL sL uL vL aC x y ==> --(&2) <= x) /\
     lcy cL sL uL vL aC <= &1 / &5 /\
     nx pow 2 + ny pow 2 = &1 /\ c1092sbs_FaceNormal cL sL nx ny
     ==> ~(ABT_upper cC sC uC vC aC nx ny <= ABT_lower cL sL uL vL aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092NMPSW_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `nx:real`; `ny:real`])
    C1092NMPSW_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aC:real`; `--nx`; `ny:real`]
    C1092SBS_LEFT_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG; REAL_ARITH `-- &2 = --(&2)`] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])] THEN
  MP_TAC(SPECL (C1092NMPSW_C @ [`--nx`; `ny:real`]) C1092NMPSW_NORTHWEST) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[REAL_NEG_NEG; c1092mcs_quarter; REAL_POW_NEG; ARITH] THEN ASM_REAL_ARITH_TAC;
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])] THEN
  C1092NMPSW_PROD `&0 <= ny * (&1 / &5 - lcy cL sL uL vL aC)` THEN
  C1092NMPSW_LIN);;

(* Lean: left_order *)
let C1092NMPSW_LEFT_ORDER = prove
 (`forall cC sC uC vC aC cL sL uL vL aL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aC /\ aC = aL /\ c1092nmpsw_data cC sC uC vC aC /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\ linside cL sL uL vL aL (--(&1)) (&0) /\
     (forall x y. linside cL sL uL vL aL x y ==> --(&2) <= x) /\
     ldisj cC sC uC vC aC cL sL uL vL aL
     ==> &1 / &5 < lcy cL sL uL vL aL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aL`)) THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[c1092nmpsw_data] (ASSUME `c1092nmpsw_data cC sC uC vC aC`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (can (term_match [] `c977cc_normal c s`) o concl)) THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL (C1092NMPSW_C @ C1092NMPSW_L) C1092MPBEB_DIRECTED_FACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `nx:real` (X_CHOOSE_THEN `ny:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 DISJ_CASES_TAC ASSUME_TAC)))) THENL
   [ALL_TAC;
    MP_TAC(SPECL (C1092NMPSW_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`;
                                  `nx:real`; `ny:real`]) C1092NMPSW_BOUNDARY) THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL (C1092NMPSW_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`;
                                `nx:real`; `ny:real`]) C1092NMPSW_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (can (term_match [] `c1092sbs_FaceNormal a b c d`) o concl)) THEN
  REWRITE_TAC[c1092sbs_FaceNormal] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
  TRY ASM_REAL_ARITH_TAC THEN
  MP_TAC(SPECL (C1092NMPSW_C @ [`cL:real`; `sL:real`; `uL:real`; `vL:real`]) C1092NMPSW_CENTRAL) THEN
  ASM_REWRITE_TAC[]);;

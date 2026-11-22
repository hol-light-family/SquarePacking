(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualNonordinaryFar.lean            *)
(* (N12Compact.C1092MPPMActualNonordinary).  ELBOW-EXCLUSION Theorem 2.      *)
(* Squares C, E, L are cC sC uC vC aC etc. (single-square statements use     *)
(* c s u v a).  SuccessorFaces is c1092mane_successorFaces, Profile is       *)
(* c1092ep_profile, Normal is c977cc_normal; successor_faces / _axes are     *)
(* C1092MANE_*; the scalar margins are C1092MANS_* / C1092MANF_*; the support *)
(* formulas are C1092WS_LOWER_NN / _PN and C1092TFSU_UPPER_POS_NEG / _POS;   *)
(* IncreasingSegmentAvoidance.dichotomy is ISA_DICHOTOMY.  Tag C1092MANFR_.  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinaryElbow.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinaryFarScalars.ml";;
needs "n12/geometry/IncreasingSegmentAvoidance.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;

let C1092MANFR_LIN = REPEAT CONJ_TAC THEN FIRST [REAL_ARITH_TAC; NLIN_TAC ~deg2:false []];;

let C1092MANFR_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC]) tms;;

let C1092MANFR_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C1092MANFR_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside; TAUT `(~p ==> false) <=> p`] THEN C1092MANFR_LIN;;

let C1092MANFR_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

(* Lean: far_successor_faces *)
let C1092MANFR_FAR_SUCCESSOR_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\
     c1092mane_successorFaces c s u v a /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\ linside c s u v a (&13 / &50) (--(&1)) /\
     ~linside c s u v a (&1) (--(&14 / &25))
     ==> v + a <= --s - (&14 / &25) * c /\ &60 * c < &91 * --s /\ c < &91 / &109`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mane_successorFaces] THEN STRIP_TAC THEN
  C1092MANFR_NORMAL_TAC THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (&7 / &20) (--(&7 / &20))`; `linside c s u v a (&13 / &50) (--(&1))`] THEN
  SUBGOAL_THEN `&0 < --s` ASSUME_TAC THENL [C1092MANFR_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `c - (&14 / &25) * s < u + a` ASSUME_TAC THENL
   [C1092MANFR_CONTRA THEN
    C1092MANFR_PROD_TAC [`&0 < (c - (&3 / &50) * s - &1) * (&1 + c)`;
                         `&0 <= --s * (&1 - c)`] THEN
    SUBGOAL_THEN `--s < &3 / &25` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN NLIN_TAC []; ALL_TAC] THEN
    C1092MANFR_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s - (&14 / &25) * c` ASSUME_TAC THENL
   [C1092MANFR_CONTRA THEN C1092MANFR_MISS_TAC `~linside c s u v a (&1) (--(&14 / &25))`;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC C1092MANF_FAR_ANGLE THEN
  ASM_REWRITE_TAC[] THEN C1092MANFR_LIN);;

(* Lean: left_segment *)
let C1092MANFR_LEFT_SEGMENT = prove
 (`forall c s u v a cL sL uL vL aL.
     c * c + s * s = &1 /\ &0 < a /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     c1092ep_profile c s u v a /\
     linside c s u v a (--(&1)) (--(&13 / &50)) /\ linside c s u v a (--(&13 / &50)) (&0) /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\ linside cL sL uL vL aL (--(&1)) (&13 / &50) /\
     ldisj c s u v a cL sL uL vL aL
     ==> v + a <= (&543 / &500) * s \/
         --(&7059 / &25000) <= ((&13 / &50) * c - (&43 / &500) * s) * u -
                              ((&13 / &50) * s + (&43 / &500) * c) * (v + a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092ep_profile] THEN STRIP_TAC THEN
  C1092MANFR_NORMAL_TAC THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside c s u v a (--(&1)) (--(&13 / &50))`; `linside c s u v a (--(&13 / &50)) (&0)`] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `--(&543 / &500)`; `&0`; `--(&1)`; `&13 / &50`] ISA_DICHOTOMY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN C1092MANFR_LIN;
    DISJ2_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN C1092MANFR_LIN]);;

(* Lean: far_impossible *)
let C1092MANFR_FAR_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cL sL uL vL aL.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aC /\ aC = aE /\ c1092ep_profile cC sC uC vC aC /\ c977cc_normal cE (--sE) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\ linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
     ~linside cE sE uE vE aE (&1) (--(&2 / &5)) /\ ~linside cE sE uE vE aE (&1) (--(&1)) /\
     ~linside cE sE uE vE aE (&0) (--(&543 / &500)) /\
     ~linside cE sE uE vE aE (&1) (--(&14 / &25)) /\
     linside cL sL uL vL aL (--(&543 / &500)) (&0) /\ linside cL sL uL vL aL (--(&1)) (&13 / &50) /\
     ldisj cC sC uC vC aC cE sE uE vE aE /\ ldisj cC sC uC vC aC cL sL uL vL aL
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092MANE_SUCCESSOR_FACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aC` THEN
    UNDISCH_TAC `c1092ep_profile cC sC uC vC aC` THEN
    REWRITE_TAC[c1092ep_profile; ldisj] THEN MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`]
    C1092MANFR_FAR_SUCCESSOR_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] C1092MANFR_LEFT_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  UNDISCH_TAC `c1092ep_profile cC sC uC vC aC` THEN REWRITE_TAC[c1092ep_profile] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `c1092mane_successorFaces cE sE uE vE aC` THEN
  REWRITE_TAC[c1092mane_successorFaces] THEN STRIP_TAC THEN
  C1092MANFR_NORMAL_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092MANE_SUCCESSOR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092MANS_RELATIVE_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[REAL_MUL_RNEG; REAL_SUB_RNEG] THEN STRIP_TAC] THEN
  C1092MANFR_PROD_TAC [`&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) + (cC * --sE + sC * cE))`;
                       `&0 <= (cC * --sE + sC * cE) * cE`] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `uE:real`)) (concl th))) THENL
   [(* C's longitudinal axis *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                  `cC * cE + sC * sE`; `cC * --sE + sC * cE`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092MANS_SOURCE_LONGITUDINAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
    C1092MANFR_PROD_TAC
     [`&0 <= (cC * cE + sC * sE) * (cE - sE - aC - uE)`;
      `&0 <= (cC * --sE + sC * cE) * (--sE - (&14 / &25) * cE - aC - vE)`] THEN
    C1092MANFR_LIN;
    (* C's transverse axis *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC`;
                  `cC * --sE + sC * cE`; `--(cC * cE + sC * sE)`] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
    MP_TAC(REWRITE_RULE[REAL_NEG_NEG]
      (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sC`; `cC:real`]
        OCWPVG_UPPER_NEG)) THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092MANF_FAR_SOURCE_TRANSVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
    C1092MANFR_PROD_TAC
     [`&0 <= (cC * --sE + sC * cE) * (cE - sE - aC - uE)`;
      `&0 <= (cC * cE + sC * sE) * (vE + (&543 / &500) * cE)`] THEN
    C1092MANFR_LIN;
    (* E's longitudinal axis *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
                  `cC * cE + sC * sE`; `--(cC * --sE + sC * cE)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj(concl th) && can (find_term ((=) `&7059 / &25000`)) (concl th))) THENL
     [MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092MANF_FAR_TRANSVERSE_SEGMENT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
      C1092MANFR_PROD_TAC
       [`&0 <= (cC * cE + sC * sE) * (uC + cC + (&2 / &5) * sC)`;
        `&0 <= (cC * --sE + sC * cE) * ((&543 / &500) * sC - aC - vC)`] THEN
      C1092MANFR_LIN;
      MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092MANF_FAR_OBLIQUE_SEGMENT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
      SUBGOAL_THEN `(cC * cE + sC * sE) * ((&13 / &50) * sC + (&43 / &500) * cC) -
                    (cC * --sE + sC * cE) * ((&13 / &50) * cC - (&43 / &500) * sC) =
                    (&43 / &500) * cE + (&13 / &50) * sE` ASSUME_TAC THENL
       [UNDISCH_TAC `cC * cC + sC * sC = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      C1092MANFR_PROD_TAC
       [`&0 < (cC * --sE + sC * cE) * (((&13 / &50) * sC + (&43 / &500) * cC) +
                                       ((&13 / &50) * cC - (&43 / &500) * sC))`] THEN
      C1092MANFR_PROD_TAC
       [`&0 <= ((&13 / &50) * sC + (&43 / &500) * cC) *
               (uE - ((cC * cE + sC * sE) * (uC + aC) + --(cC * --sE + sC * cE) * vC))`;
        `&0 <= ((&13 / &50) * sC + (&43 / &500) * cC) * (cE - sE - aC - uE)`;
        `&0 <= (cC * --sE + sC * cE) *
               (((&13 / &50) * cC - (&43 / &500) * sC) * uC -
                ((&13 / &50) * sC + (&43 / &500) * cC) * (vC + aC) + &7059 / &25000)`;
        `&0 <= ((cC * --sE + sC * cE) * ((&13 / &50) * cC - (&43 / &500) * sC) -
                (cC * cE + sC * sE) * ((&13 / &50) * sC + (&43 / &500) * cC)) *
               (--(&13 / &50) * sC - aC - uC)`;
        `&0 < (aC - &1) * (((&13 / &50) * sC + (&43 / &500) * cC) +
               (cC * --sE + sC * cE) * (((&13 / &50) * sC + (&43 / &500) * cC) +
                                         ((&13 / &50) * cC - (&43 / &500) * sC)))`] THEN
      MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNU) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      C1092MANFR_LIN];
    (* E's transverse axis *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sE`; `cE:real`;
                  `cC * --sE + sC * cE`; `cC * cE + sC * sE`] C1092TFSU_UPPER_POS_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE`] C1092MANS_SUCCESSOR_TRANSVERSE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANFR_LIN; DISCH_TAC] THEN
    C1092MANFR_PROD_TAC
     [`&0 <= (cC * --sE + sC * cE) * (uC + cC + (&2 / &5) * sC)`;
      `&0 <= (cC * cE + sC * sE) * (vC + cC - (&2 / &5) * sC)`] THEN
    C1092MANFR_LIN]);;

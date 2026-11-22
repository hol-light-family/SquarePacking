(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NegativeCornerFloor.lean             *)
(* (N12Compact.C1092MMMPNegativeCornerFloor).  The actual negative left-wall *)
(* square L (cL sL uL vL aL) forces the corner K's (cK sK uK vK aK) scaled  *)
(* lower transverse face.  centerX/centerY are lcx/lcy; Normal is            *)
(* c977cc_normal; NegativeCenterSupports alternatives / up_right are        *)
(* C1092MNCS_*; CenterCorner.up_left is C1092MMCC_UP_LEFT; upward is         *)
(* C1092MCSUP_UPWARD; elementary is C1092MCS_ELEMENTARY; lower_nn / lower_np *)
(* are C1092WS_*.  Tag C1092MMNCF_.                                          *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_NegativeCenterSupports.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;

let C1092MMNCF_LIN = REPEAT CONJ_TAC THEN FIRST [REAL_ARITH_TAC; NLIN_TAC ~deg2:false []; RASM_ARITH_TAC];;

let C1092MMNCF_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC]) tms;;

let C1092MMNCF_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C1092MMNCF_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside; TAUT `(~p ==> false) <=> p`] THEN C1092MMNCF_LIN;;

let C1092MMNCF_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns);;

(* Lean: positive_pair_scalar (private) *)
let C1092MMNCF_POSITIVE_PAIR_SCALAR = prove
 (`forall d r c s. c977cc_normal d r /\ c977cc_normal c s
     ==> r * ((&1 / &5) * c pow 2 + (&1 / &2) * c * s - c) +
         d * (&1 / &2 + (&1 / &2) * s pow 2 - s + (&1 / &5) * c * s) <=
         d / &2 - (&3 / &5) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092MCS_ELEMENTARY) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN C1092MMNCF_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN REWRITE_TAC[REAL_POW_2] THEN
  C1092MMNCF_PROD_TAC [`&0 <= (c + s - &1) * (&10 / &7 - (c + s))`; `&0 <= c * s`;
                       `&0 <= s * (c - s)`; `&0 <= s * (&1 - s / &2 - c / &5)`] THEN
  SUBGOAL_THEN `&1 + (&4 / &5) * c * s <= c + s` ASSUME_TAC THENL
   [C1092MMNCF_LIN; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 / &2) * s * s - s + (&1 / &5) * c * s <= &0 /\
                (&1 / &5) * c * c + (&1 / &2) * c * s - c +
                (&1 / &2 + (&1 / &2) * s * s - s + (&1 / &5) * c * s) + &1 / &10 <= &0`
  STRIP_ASSUME_TAC THENL [C1092MMNCF_LIN; ALL_TAC] THEN
  C1092MMNCF_PROD_TAC
   [`&0 <= (d - r) * --((&1 / &2) * s * s - s + (&1 / &5) * c * s)`;
    `&0 <= r * --((&1 / &5) * c * c + (&1 / &2) * c * s - c +
                 (&1 / &2 + (&1 / &2) * s * s - s + (&1 / &5) * c * s) + &1 / &10)`] THEN
  C1092MMNCF_LIN);;

(* Lean: nonnegative_impossible *)
let C1092MMNCF_NONNEGATIVE_IMPOSSIBLE = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL (--sL) /\ sL < &0 /\
     lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     (forall x y. linside cL sL uL vL aL x y ==> --(&1) <= x) /\
     c977cc_normal cK sK /\ linside cL sL uL vL aL (&0) (&2 / &5) /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aK`)) THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] C1092MNCS_ALTERNATIVES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
      check (fun th -> concl th = `c977cc_normal cK sK`)) THEN C1092MMNCF_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`; `cL:real`; `--sL`]
    C1092MNCS_UP_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `--sL`; `cK:real`; `sK:real`] C1092MMNCF_POSITIVE_PAIR_SCALAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MMNCF_NORMAL_TAC THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cK sK uK vK aK (&0) (&1 / &2)`; `linside cK sK uK vK aK (&0) (&1)`] THEN
  SUBGOAL_THEN `uK + aK <= (&1 / &5) * cK + sK` ASSUME_TAC THENL
   [C1092MMNCF_CONTRA THEN C1092MMNCF_MISS_TAC `~linside cK sK uK vK aK (&1 / &5) (&1)`;
    ALL_TAC] THEN
  C1092MMNCF_PROD_TAC [`&0 < --sL * cK`; `&0 <= cL * sK`; `&0 <= cL * (cK - sK)`;
                       `&0 <= sK * (cL - --sL)`] THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `uK:real`)) (concl th))) THENL
   [MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `--sL`; `cL:real`;
                  `--sL * cK + cL * sK`; `cL * cK - --sL * sK`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MMNCF_LIN; DISCH_TAC] THEN
    C1092MMNCF_PROD_TAC
     [`&0 < (--sL * cK + cL * sK) * (((&1 / &5) * cK + sK - &1) - uK)`;
      `&0 <= (cL * cK - --sL * sK) * (cK / &2 - vK)`;
      `&0 <= (aK - &1) * (cL + --sL)`] THEN
    SUBGOAL_THEN `(--sL * cK + cL * sK) * ((&1 / &5) * cK + sK - &1) +
                  (cL * cK - --sL * sK) * (cK / &2) =
        --sL * ((&1 / &5) * cK pow 2 + (&1 / &2) * cK * sK - cK) +
        cL * (&1 / &2 + (&1 / &2) * sK pow 2 - sK + (&1 / &5) * cK * sK)` ASSUME_TAC THENL
     [UNDISCH_TAC `cK * cK + sK * sK = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    C1092MMNCF_LIN;
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`;
                  `&0`; `&2 / &5`; `cK:real`; `sK:real`] ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN C1092MMNCF_LIN;
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`; `--sK`; `cK:real`]
      C1092MMCC_UP_LEFT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C1092MMNCF_LIN; DISCH_TAC] THEN
    C1092MMNCF_LIN]);;

(* the three separating alternatives with the two shared consequences *)
let C1092MMNCF_SETUP_BODY_TAC =
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aK`)) THEN
  C1092MMNCF_NORMAL_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] C1092MNCS_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MMNCF_LIN; DISCH_TAC] THEN
  MAP_EVERY (fun tm -> MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC)
   [`linside cK sK uK vK aK (&0) (&1 / &2)`; `linside cK sK uK vK aK (&0) (&1)`;
    `linside cL sL uL vL aK (&0) (&2 / &5)`] THEN
  C1092MMNCF_PROD_TAC [`&0 <= --sL * --sK`; `&0 < cL * cK`; `&0 <= cL * --sK`];;

let C1092MMNCF_SETUP_TAC = REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MMNCF_SETUP_BODY_TAC;;

(* Lean: upper_u (private) *)
let C1092MMNCF_UPPER_U = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL = aK /\ c977cc_normal cL (--sL) /\
     lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     c977cc_normal cK (--sK) /\ linside cL sL uL vL aL (&0) (&2 / &5) /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> uK + aK <= cK / &5 + sK`,
  C1092MMNCF_SETUP_TAC THEN
  C1092MMNCF_CONTRA THEN
  SUBGOAL_THEN `vK + aK <= cK + --sK / &5` ASSUME_TAC THENL
   [C1092MMNCF_CONTRA THEN C1092MMNCF_MISS_TAC `~linside cK sK uK vK aK (&1 / &5) (&1)`;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `--sK`] C1092MCS_ELEMENTARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `uK:real`)) (concl th))) THENL
   [C1092MMNCF_PROD_TAC
     [`&0 < (--sL * --sK + cL * cK) * ((cK + --sK / &5 - &1) - vK)`;
      `&0 <= --sK * (&1 - --sK / &5)`] THEN
    C1092MMNCF_PROD_TAC
     [`&0 <= --sL * --((--sK) * (--sK) / &5 - --sK)`;
      `&0 < cL * (cK - cK * --sK / &5 - &3 / &5)`] THEN
    ASM_CASES_TAC `&0 <= --sL * cK - cL * --sK` THENL
     [MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `--sL`; `cL:real`;
                    `--sL * cK - cL * --sK`; `--sL * --sK + cL * cK`] C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MMNCF_LIN; DISCH_TAC] THEN
      C1092MMNCF_PROD_TAC [`&0 <= (--sL * cK - cL * --sK) * (--(--sK) - uK)`];
      MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `--sL`; `cL:real`;
                    `--sL * cK - cL * --sK`; `--sL * --sK + cL * cK`] C1092WS_LOWER_NP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MMNCF_LIN; DISCH_TAC] THEN
      C1092MMNCF_PROD_TAC [`&0 <= --(--sL * cK - cL * --sK) * ((uK + aK) - --(--sK))`]] THEN
    (SUBGOAL_THEN `(--sL * cK - cL * --sK) * --(--sK) + (--sL * --sK + cL * cK) * (cK + --sK / &5 - &1) =
        --sL * ((--sK) * (--sK) / &5 - --sK) + cL * (&1 - cK + cK * --sK / &5)` ASSUME_TAC THENL
     [UNDISCH_TAC `cK * cK + sK * sK = &1` THEN CONV_TAC REAL_RING; ALL_TAC]) THEN
    C1092MMNCF_LIN;
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`;
                  `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `cK:real`; `sK:real`]
      C1092MCSUP_UPWARD) THEN
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] ABT_OWNU) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    C1092MMNCF_LIN;
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`;
                  `&0`; `&2 / &5`; `--sK`; `cK:real`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN C1092MMNCF_LIN; STRIP_TAC] THEN
    C1092MMNCF_LIN]);;

(* Lean: floor *)
let C1092MMNCF_FLOOR = prove
 (`forall cL sL uL vL aL cK sK uK vK aK.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     &1 < aL /\ aL <= &2 /\ aL = aK /\ c977cc_normal cL (--sL) /\
     lcx cL sL uL vL aL <= &0 /\ &0 <= lcy cL sL uL vL aL /\
     (forall x y. linside cL sL uL vL aL x y ==> --(&1) <= x) /\
     c977cc_normal cK (--sK) /\ linside cL sL uL vL aL (&0) (&2 / &5) /\
     linside cK sK uK vK aK (&0) (&1 / &2) /\ linside cK sK uK vK aK (&0) (&1) /\
     ~linside cK sK uK vK aK (&1 / &5) (&1) /\
     ldisj cL sL uL vL aL cK sK uK vK aK
     ==> aK * (cK + --sK) / &2 - --sK <= vK`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] C1092MMNCF_UPPER_U) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `cL:real`; `--sL`]
    C1092MNCS_UP_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`; `cK:real`; `--sK`]
    C1092MNCS_UP_RIGHT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  C1092MMNCF_SETUP_BODY_TAC THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (fun th ->
    is_disj(concl th) && can (find_term ((=) `uK:real`)) (concl th))) THENL
   [C1092MMNCF_CONTRA THEN
    C1092MMNCF_PROD_TAC
     [`&0 < (--sL * --sK + cL * cK) * ((aK * (cK + --sK) / &2 - --sK) - vK)`] THEN
    ASM_CASES_TAC `&0 <= --sL * cK - cL * --sK` THENL
     [MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `--sL`; `cL:real`;
                    `--sL * cK - cL * --sK`; `--sL * --sK + cL * cK`] C1092WS_LOWER_NN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MMNCF_LIN; DISCH_TAC] THEN
      C1092MMNCF_PROD_TAC
       [`&0 <= (--sL * cK - cL * --sK) * ((cK / &5 - --sK - aK) - uK)`;
        `&0 <= (aK - &1) * (&1 + (cK - --sK) / &2)`] THEN
      SUBGOAL_THEN `cK / &5 - aK + (&1 - aK / &2) * (cK - --sK) <= &0` ASSUME_TAC THENL
       [C1092MMNCF_LIN; ALL_TAC] THEN
      C1092MMNCF_PROD_TAC
       [`&0 <= (--sL * cK - cL * --sK) * --(cK / &5 - aK + (&1 - aK / &2) * (cK - --sK))`] THEN
      SUBGOAL_THEN `(--sL * cK - cL * --sK) * (cK / &5 - --sK - aK) +
          (--sL * --sK + cL * cK) * (aK * (cK + --sK) / &2 - --sK) -
          (aK * (cL + --sL) / &2 - --sL) =
          (--sL * cK - cL * --sK) * (cK / &5 - aK + (&1 - aK / &2) * (cK - --sK))` ASSUME_TAC THENL
       [UNDISCH_TAC `cK * cK + sK * sK = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      C1092MMNCF_LIN;
      MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `--sL`; `cL:real`;
                    `--sL * cK - cL * --sK`; `--sL * --sK + cL * cK`] C1092WS_LOWER_NP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MMNCF_LIN; DISCH_TAC] THEN
      C1092MMNCF_PROD_TAC
       [`&0 <= --(--sL * cK - cL * --sK) * ((uK + aK) - --(--sK) / &2)`;
        `&0 <= (&2 - aK) * (cK - --sK)`] THEN
      SUBGOAL_THEN `&0 <= cK - --sK / &2 - aK * (cK - --sK) / &2` ASSUME_TAC THENL
       [C1092MMNCF_LIN; ALL_TAC] THEN
      C1092MMNCF_PROD_TAC
       [`&0 <= --(--sL * cK - cL * --sK) * (cK - --sK / &2 - aK * (cK - --sK) / &2)`] THEN
      SUBGOAL_THEN `(--sL * cK - cL * --sK) * (--(--sK) / &2) +
          (--sL * --sK + cL * cK) * (aK * (cK + --sK) / &2 - --sK) -
          (aK * (cL + --sL) / &2 - --sL) =
          (--sL * cK - cL * --sK) * (cK - --sK / &2 - aK * (cK - --sK) / &2)` ASSUME_TAC THENL
       [UNDISCH_TAC `cK * cK + sK * sK = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
      C1092MMNCF_LIN];
    MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aK:real`;
                  `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`; `cK:real`; `sK:real`]
      C1092MCSUP_UPWARD) THEN
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] ABT_OWNU) THEN
    ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    C1092MMNCF_LIN;
    C1092MMNCF_LIN]);;

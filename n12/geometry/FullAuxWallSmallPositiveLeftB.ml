(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallSmallPositiveLeftB.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.FullAuxWallSmallPositiveLeftB).  The     *)
(* neighbor-owned longitudinal separator is also impossible for a small     *)
(* positive left-wall frame.  Normal is c977cc_normal; upper / lower are     *)
(* ABT_upper / ABT_lower; cosine_order: C977CSB_COSINE_ORDER;                *)
(* FourSquareBLBridge.left_wall: FSBL_LEFT_WALL; FullAuxWallPositiveLeftAxes.*)
(* alternatives: FAWPLX_ALTERNATIVES; FullAuxWallSmallPositiveLeft.no_left_u:*)
(* FAWSPL_NO_LEFT_U.  The Lean local abbreviations alpha, h are written out. *)
(* The OpenSquare invariants are explicit hypotheses.  Tag FAWSPLB_.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FullAuxWallSmallPositiveLeft.ml";;

let FAWSPLB_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL
  [CONJ_TAC THEN FIRST [REWRITE_TAC[REAL_LE_POW_2] THEN NO_TAC; RASM_ARITH_TAC];
   DISCH_TAC];;

(* Lean: polynomial (private) *)
let fawsplb_polynomial = new_definition
 `fawsplb_polynomial (t:real) (r:real) =
    --(&2 / &5) + t - (&3 / &10) * t pow 2 - (&3 / &40) * t pow 4 +
    (&63 / &125) * r pow 2 * (&1 - t pow 2 / &2) - (&73 / &1000) * r * t`;;

(* Lean: polynomial_nonpos (private) *)
let FAWSPLB_POLYNOMIAL_NONPOS = prove
 (`forall t r. &0 <= t /\ t <= &23 / &50 /\ &0 <= r /\ r <= &4 / &25
     ==> fawsplb_polynomial t r <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(SPEC `t:real` REAL_LE_POW_2) THEN ASSUME_TAC(SPEC `r:real` REAL_LE_POW_2) THEN
  FAWSPLB_PROD_TAC `&23 / &50 - t` `&23 / &50 + t` THEN
  FAWSPLB_PROD_TAC `&4 / &25 - r` `&4 / &25 + r` THEN
  SUBGOAL_THEN `(&23 / &50) pow 2 + t pow 2 <= &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `&1 - (&23 / &50 + t)` `(&23 / &50) pow 2 + t pow 2` THEN
  SUBGOAL_THEN `(&23 / &50 + t) * ((&23 / &50) pow 2 + t pow 2) <= &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&3 / &10 + (&63 / &250) * r pow 2 <= &69 / &125` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `&3 / &10 + (&63 / &250) * r pow 2` `&1 - (&23 / &50 + t)` THEN
  SUBGOAL_THEN
   `&0 <= &1 - (&73 / &1000) * r - (&3 / &10 + (&63 / &250) * r pow 2) * (&23 / &50 + t) -
          (&3 / &40) * (&23 / &50 + t) * ((&23 / &50) pow 2 + t pow 2)` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `&23 / &50 - t`
   `&1 - (&73 / &1000) * r - (&3 / &10 + (&63 / &250) * r pow 2) * (&23 / &50 + t) -
    (&3 / &40) * (&23 / &50 + t) * ((&23 / &50) pow 2 + t pow 2)` THEN
  SUBGOAL_THEN
   `fawsplb_polynomial (&23 / &50) r - fawsplb_polynomial t r =
    (&23 / &50 - t) *
    (&1 - (&73 / &1000) * r - (&3 / &10 + (&63 / &250) * r pow 2) * (&23 / &50 + t) -
     (&3 / &40) * (&23 / &50 + t) * ((&23 / &50) pow 2 + t pow 2))` ASSUME_TAC THENL
  [REWRITE_TAC[fawsplb_polynomial] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `fawsplb_polynomial (&23 / &50) (&0) <= &0 /\
                fawsplb_polynomial (&23 / &50) (&4 / &25) <= &0` STRIP_ASSUME_TAC THENL
  [REWRITE_TAC[fawsplb_polynomial] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&4 / &25 - r) * fawsplb_polynomial (&23 / &50) (&0) +
    r * fawsplb_polynomial (&23 / &50) (&4 / &25) -
    (&4 / &25) * fawsplb_polynomial (&23 / &50) r =
    (&4 / &25) * (&63 / &125) * (&1 - (&23 / &50) pow 2 / &2) * r * (&4 / &25 - r)`
    ASSUME_TAC THENL
  [REWRITE_TAC[fawsplb_polynomial] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `&4 / &25 - r` `--fawsplb_polynomial (&23 / &50) (&0)` THEN
  FAWSPLB_PROD_TAC `r:real` `--fawsplb_polynomial (&23 / &50) (&4 / &25)` THEN
  FAWSPLB_PROD_TAC `r:real` `&4 / &25 - r` THEN
  SUBGOAL_THEN `fawsplb_polynomial (&23 / &50) r <= &0` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: margin (private) *)
let FAWSPLB_MARGIN = prove
 (`forall l r b t. c977cc_normal l r /\ c977cc_normal b t /\ r <= &4 / &25 /\ t <= &23 / &50
     ==> l * ((&8 / &5 - l) * b + (&1 - r) * t - &1) + (&457 / &500) * r * t <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWSPL_NORMAL_TAC THEN
  FAWSPLB_PROD_TAC `&4 / &25 - r` `&4 / &25 + r` THEN
  SUBGOAL_THEN `&493 / &500 <= l` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FAWSPLB_PROD_TAC `&493 / &500 - l` `&493 / &500 + l` THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `&1 - l` `(&63 / &125) * l - &62 / &125` THEN
  SUBGOAL_THEN `&1 - l <= (&63 / &125) * r pow 2` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&457 / &500 <= (&927 / &1000) * l` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `&1 - b` `&3 + b` THEN
  FAWSPLB_PROD_TAC `(&1 - b) pow 2` `(&1 - b) * (&3 + b)` THEN
  SUBGOAL_THEN `&8 * (&1 - b) - &4 * t pow 2 - t pow 4 = (&1 - b) pow 3 * (&3 + b)`
    ASSUME_TAC THENL
  [UNDISCH_TAC `b pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `b <= &1 - t pow 2 / &2 - t pow 4 / &8` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `b <= &1 - t pow 2 / &2` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `b - &1`]; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `b:real` `(&63 / &125) * r pow 2 - (&1 - l)` THEN
  FAWSPLB_PROD_TAC `r pow 2` `(&1 - t pow 2 / &2) - b` THEN
  FAWSPLB_PROD_TAC `r:real` `t:real` THEN
  FAWSPLB_PROD_TAC `r * t` `(&927 / &1000) * l - &457 / &500` THEN
  SUBGOAL_THEN
   `(&3 / &5) * b + t - &1 + b * (&1 - l) - (&73 / &1000) * r * t <= fawsplb_polynomial t r`
    ASSUME_TAC THENL
  [REWRITE_TAC[fawsplb_polynomial] THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `l:real`
   `fawsplb_polynomial t r - ((&3 / &5) * b + t - &1 + b * (&1 - l) - (&73 / &1000) * r * t)` THEN
  MP_TAC(SPECL [`t:real`; `r:real`] FAWSPLB_POLYNOMIAL_NONPOS) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  FAWSPLB_PROD_TAC `l:real` `--fawsplb_polynomial t r` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: no_neighbor_u *)
let FAWSPLB_NO_NEIGHBOR_U = prove
 (`forall cL sL uL vL aL cB sB uB (vB:real) aB.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cL sL /\ c977cc_normal cB sB /\ aL = aB /\ &1 < aB /\
     sL <= &4 / &25 /\ &3 / &10 < sB /\ sB <= &23 / &50 /\
     lcont cL sL uL vL aL /\ linside cL sL uL vL aL (&457 / &500) (&2) /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\
     ABT_upper cL sL uL vL aL cB sB <= uB
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aL:real = aB`)) THEN
  FAWSPL_NORMAL_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `cL:real`; `sL:real`] C977CSB_COSINE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 < cL /\ &0 < cB` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cL * cB + sL * sB` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cL * sB - sL * cB` ASSUME_TAC THENL
  [MP_TAC(SPECL [`cL:real`; `sB - sL`] REAL_LT_MUL) THEN
   ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
   FAWSPLB_PROD_TAC `sL:real` `cL - cB` THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  (* support *)
  SUBGOAL_THEN `ABT_upper cL sL uL vL aB cB sB =
                (cL * cB + sL * sB) * (uL + aB) + (cL * sB - sL * cB) * (vL + aB)`
    ASSUME_TAC THENL
  [REWRITE_TAC[C977NCO_UPPER_IN_BANDS] THEN
   SUBGOAL_THEN `abs(cB * cL + sB * sL) = cL * cB + sL * sB /\
                 abs(--cB * sL + sB * cL) = cL * sB - sL * cB`
     (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH `x = y /\ &0 < y ==> abs x = y`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  (* the left wall *)
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aB:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[lcx] THEN
  SUBGOAL_THEN `abs sL = sL` SUBST1_TAC THENL [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= cL * uL - sL * (vL + aB)` ASSUME_TAC THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `cL * cB + sL * sB` `cL * uL - sL * (vL + aB)` THEN
  STRIP_ASSUME_TAC(REWRITE_RULE[linside]
    (ASSUME `linside cL sL uL vL aB (&457 / &500) (&2)`)) THEN
  FAWSPLB_PROD_TAC `sB:real` `(vL + aB) - (--sL * (&457 / &500) + cL * &2)` THEN
  SUBGOAL_THEN
   `cL * ABT_upper cL sL uL vL aB cB sB - cL * (cL * cB + sL * sB) * aB - sB * (vL + aB) =
    (cL * cB + sL * sB) * (cL * uL - sL * (vL + aB))` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `cL * cL + sL * sL = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  SUBGOAL_THEN
   `cL * (cL * cB + sL * sB) * aB + &2 * cL * sB - (&457 / &500) * sL * sB <=
    cL * ABT_upper cL sL uL vL aB cB sB` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWSPLB_PROD_TAC `cL:real` `uB - ABT_upper cL sL uL vL aB cB sB` THEN
  FAWSPLB_PROD_TAC `cL:real` `(&8 / &5) * cB + &3 * sB - (uB + aB)` THEN
  SUBGOAL_THEN `&0 < cL * (&1 + (cL * cB + sL * sB))` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cL * (&1 + (cL * cB + sL * sB))`; `aB - &1`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `cB:real`; `sB:real`] FAWSPLB_MARGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: sine *)
let FAWSPLB_SINE = prove
 (`forall cL sL uL vL aL cB sB uB vB aB.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cL sL /\ c977cc_normal cB sB /\ aL = aB /\ &1 < aB /\
     &3 / &10 < sB /\ sB <= &23 / &50 /\
     lcont cL sL uL vL aL /\ linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cL sL uL vL aL (&1) (&8 / &5) /\ linside cB sB uB vB aB (&1) (&12 / &5) /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     (&457 / &500) * cB + &2 * sB <= uB /\
     &1 < (&343 / &500) * cB + sB /\
     ldisj cL sL uL vL aL cB sB uB vB aB
     ==> &4 / &25 < sL`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWPLX_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THENL
  [MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWSPL_NO_LEFT_U) THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
   MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                 `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWSPLB_NO_NEIGHBOR_U) THEN
   ASM_REWRITE_TAC[]]);;

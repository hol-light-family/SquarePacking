(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastNegativePair.lean                      *)
(* (N12Compact.C981CompletionLastNegativePair).  The full actual two-square *)
(* negative-central ending for the final two C981 vectors.  C has sC = --r  *)
(* with c977cc_normal cC r; the Lean lets alpha, k, K, G, u, v are written  *)
(* out; cut_of_cap is applied inline at its two caps.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_SteepPositivePair.ml";;
needs "n12/geometry/CP_C981_LastScalars.ml";;

let C981LNP_LIN = NLIN_TAC ~deg2:false [];;

let C981LNP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C981LNP_LIN; ALL_TAC];;

let C981LNP_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C981LNP_LIN; ALL_TAC];;

let C981LNP_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C981LNP_RING tm unit = SUBGOAL_THEN tm ASSUME_TAC THENL
  [UNDISCH_TAC unit THEN CONV_TAC REAL_RING; ALL_TAC];;

let C981LNP_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: positive_v (private) *)
let C981LNP_POSITIVE_V = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ c977cc_normal cB sB /\ &1 < aB /\
     linside cC sC uC vC aC (&2) (&2) /\ linside cC sC uC vC aC (&3 / &2) (&2) /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     (vC + aC <= ABT_lower cB sB uB vB aB r cC \/
      ABT_upper cC sC uC vC aC (--sB) cB <= vB)
     ==> &3 * cB - (&8 / &5) * sB < vB + aB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --r`)) THEN
  C981SPP_NORMALS_TAC THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cB` STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C981LNP_LIN; ALL_TAC] THEN
  C981LNP_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&2)` THEN
  C981LNP_UNFOLD_TAC `linside cB sB uB vB aB (&1) (&113 / &50)` THEN
  C981LNP_CONTRA THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C981LNP_PROD `&0 <= cB * (cC - r)` THEN
    C981LNP_PROD `&0 <= r * (cB - sB)` THEN
    C981LNP_PROD `&0 <= cB * r` THEN
    C981LNP_PROD `&0 <= sB * cC` THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`; `cC:real`]
      C981NPR_LOWER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C981LNP_LIN; DISCH_TAC] THEN
    C981LNP_PROD `&0 <= (cB * r + sB * cC) * ((cB + (&113 / &50) * sB) - uB)` THEN
    C981LNP_PROD `&0 <= (cB * cC - sB * r) * ((&3 * cB - (&8 / &5) * sB - &1) - vB)` THEN
    C981LNP_PROD `&0 <= (&1 - cB) * (&3 * cB - &2)` THEN
    C981LNP_FACT `&1 - cB <= (&3 / &5) * sB * sB` THEN
    C981LNP_PROD `&0 <= sB * sB` THEN
    C981LNP_PROD `&0 <= cB * sB` THEN
    C981LNP_PROD `&0 <= sB * (cB - sB)` THEN
    C981LNP_FACT `&1 - cB - (&37 / &50) * sB * sB - (&3 / &5) * cB * sB <= &0` THEN
    C981LNP_FACT `--(&1) + sB + (&3 / &5) * sB * sB - (&37 / &50) * cB * sB <= &0` THEN
    C981LNP_PROD `&0 <= cC * --(&1 - cB - (&37 / &50) * sB * sB - (&3 / &5) * cB * sB)` THEN
    C981LNP_PROD `&0 <= r * --(--(&1) + sB + (&3 / &5) * sB * sB - (&37 / &50) * cB * sB)` THEN
    C981LNP_RING
     `(cB * r + sB * cC) * (cB + (&113 / &50) * sB) +
      (cB * cC - sB * r) * (&3 * cB - (&8 / &5) * sB - &1) - &2 * (cC + r) =
      cC * (&1 - cB - (&37 / &50) * sB * sB - (&3 / &5) * cB * sB) +
      r * (--(&1) + sB + (&3 / &5) * sB * sB - (&37 / &50) * cB * sB)`
     `cB * cB + sB * sB = &1` THEN
    C981LNP_LIN;
    ABT_SB_TAC [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aC:real`]
      `&3 / &2` `&2` `--sB:real` `cB:real` THEN
    C981LNP_LIN]);;

(* Lean: impossible *)
let C981LNP_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ c977cc_normal cB sB /\
     &1 < aC /\ aC = aB /\ &1 / &2 <= sB /\
     linside cC sC uC vC aC (&2) (&2) /\
     linside cC sC uC vC aC (&3 / &2) (&2) /\
     linside cC sC uC vC aC (&2) (&3 / &2) /\
     linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     ~linside cC sC uC vC aC (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&8 / &5) (&3) /\
     ~linside cB sB uB vB aB (&1) (&3) /\
     ~linside cC sC uC vC aC (&113 / &50) (&2) /\
     ~linside cC sC uC vC aC (&113 / &50) (&1) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sB` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `r:real`]
    C981NPR_CENTRAL_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`]
    C981SPP_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`]
    C981LNP_POSITIVE_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_TRANS]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C981SPP_NORMALS_TAC THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cB` STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C981LNP_LIN; ALL_TAC] THEN
  C981LNP_UNFOLD_TAC `linside cB sB uB vB aC (&33 / &20) (&47 / &20)` THEN
  C981LNP_UNFOLD_TAC `linside cB sB uB vB aC (&1) (&113 / &50)` THEN
  C981LNP_UNFOLD_TAC `linside cB sB uB vB aC (&1) (&12 / &5)` THEN
  C981LNP_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&2)` THEN
  SUBGOAL_THEN `uB + aC <= (&8 / &5) * cB + &3 * sB` ASSUME_TAC THENL
   [C981LNP_CONTRA THEN UNDISCH_TAC `~linside cB sB uB vB aC (&8 / &5) (&3)` THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981LNP_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `vB + aC <= &3 * cB - sB` ASSUME_TAC THENL
   [C981LNP_CONTRA THEN UNDISCH_TAC `~linside cB sB uB vB aC (&1) (&3)` THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981LNP_LIN;
    ALL_TAC] THEN
  C981LNP_PROD `&0 <= cB * (cC - r)` THEN
  C981LNP_PROD `&0 <= r * (cB - sB)` THEN
  C981LNP_PROD `&0 <= cB * r` THEN
  C981LNP_PROD `&0 < sB * cC` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C981LNP_PROD `&0 <= (cB + sB - &1) * (&10 / &7 - (cB + sB))` THEN
    C981LNP_PROD `&0 < cB * sB` THEN
    C981LNP_FACT `&0 < cB + sB - &1 - (&3 / &5) * cB * sB` THEN
    C981LNP_PROD `&0 <= sB * sB` THEN
    C981LNP_FACT `sB - cB - &2 / &5 - (&3 / &5) * sB * sB <= &0` THEN
    C981LNP_PROD `&0 < cC * (cB + sB - &1 - (&3 / &5) * cB * sB)` THEN
    C981LNP_PROD `&0 <= r * --(sB - cB - &2 / &5 - (&3 / &5) * sB * sB)` THEN
    C981LNP_PROD `&0 <= (cB * r + sB * cC) * (((&8 / &5) * cB + &3 * sB - &1) - uB)` THEN
    C981LNP_PROD `&0 <= (cB * cC - sB * r) * ((&3 * cB - sB - &1) - vB)` THEN
    C981LNP_RING
     `(cB * r + sB * cC) * ((&8 / &5) * cB + &3 * sB - &1) +
      (cB * cC - sB * r) * (&3 * cB - sB - &1) - &2 * (cC + r) =
      --cC * (cB + sB - &1 - (&3 / &5) * cB * sB) +
      r * (sB - cB - &2 / &5 - (&3 / &5) * sB * sB)`
     `cB * cB + sB * sB = &1` THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `r:real`; `cC:real`]
      C981NPR_LOWER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C981LNP_LIN; DISCH_TAC] THEN
    C981LNP_LIN;
    ALL_TAC] THEN
  (* the transverse mode: upper C (-sB) cB <= vB *)
  SUBGOAL_THEN `ABT_upper cC (--r) uC vC aC (--sB) cB =
                --(cB * r + sB * cC) * uC + (cB * cC - sB * r) * (vC + aC)` ASSUME_TAC THENL
   [REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(--sB * cC + cB * --r) = cB * r + sB * cC /\
                  abs(-- --sB * --r + cB * cC) = cB * cC - sB * r`
      (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC(REAL_ARITH
        `(&0 <= y /\ (x = y \/ x = --y)) ==> abs x = y`) THEN
      (CONJ_TAC THENL [C981LNP_LIN; REAL_ARITH_TAC]);
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  C981LNP_PROD `&0 <= (cB * cC - sB * r) * (vC + aC - &2 * (cC + r))` THEN
  C981LNP_PROD `&0 < (aC - &1) * (&1 + (cB * r + sB * cC))` THEN
  C981LNP_RING
   `--(cB * r + sB * cC) * uC + (cB * cC - sB * r) * (vC + aC) =
    &2 * (cB - sB) + aC * (cB * r + sB * cC) -
    (cB * r + sB * cC) * (uC + aC - &2 * (cC - r)) +
    (cB * cC - sB * r) * (vC + aC - &2 * (cC + r))`
   `cC * cC + --r * --r = &1` THEN
  (* the cap from the two missing points D, J *)
  SUBGOAL_THEN `uC + aC - &2 * (cC - r) <= (&13 / &50) * cC + r` ASSUME_TAC THENL
   [C981LNP_CONTRA THEN
    SUBGOAL_THEN `vC + aC <= (&113 / &50) * r + &2 * cC` ASSUME_TAC THENL
     [C981LNP_CONTRA THEN UNDISCH_TAC `~linside cC (--r) uC vC aC (&113 / &50) (&2)` THEN
      REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981LNP_LIN; ALL_TAC] THEN
    SUBGOAL_THEN `(&113 / &50) * r + cC <= vC` ASSUME_TAC THENL
     [C981LNP_CONTRA THEN UNDISCH_TAC `~linside cC (--r) uC vC aC (&113 / &50) (&1)` THEN
      REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981LNP_LIN; ALL_TAC] THEN
    C981LNP_LIN;
    ALL_TAC] THEN
  C981LNP_PROD `&0 <= (cB * r + sB * cC) *
                     ((&7 / &20) * (cC + r) - (uC + aC - &2 * (cC - r)))` THEN
  C981LNP_PROD `&0 <= (cB * r + sB * cC) *
                     (((&13 / &50) * cC + r) - (uC + aC - &2 * (cC - r)))` THEN
  MP_TAC(SPECL [`cC:real`; `r:real`; `cB:real`; `sB:real`] C981LS_NEGATIVE_IMPOSSIBLE) THEN
  MATCH_MP_TAC(TAUT `p ==> (p ==> false) ==> false`) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN REPEAT CONJ_TAC THEN C981LNP_LIN);;

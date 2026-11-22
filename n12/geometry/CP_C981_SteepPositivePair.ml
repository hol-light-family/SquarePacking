(* ========================================================================= *)
(* Port of Compact/Completion/C981/SteepPositivePair.lean                     *)
(* (N12Compact.C981CompletionSteepPositivePair).  C981-COMMON-CYCLE Theorem  *)
(* 3: the actual negative central square cannot separate from the steep      *)
(* positive neighbouring central square.  C has sC = --r with                *)
(* c977cc_normal cC r.  The Lean lets alpha, k, F, G, K, u, v are written   *)
(* out.  short_projections is WFP_SHORT_PROJECTIONS; half is c981ha_half.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C981_NegativePair.ml";;
needs "n12/geometry/CP_C981_AngularScalars.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;

let C981SPP_LIN = NLIN_TAC ~deg2:false [];;

let C981SPP_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C981SPP_LIN; ALL_TAC];;

let C981SPP_FACT tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C981SPP_LIN; ALL_TAC];;

let C981SPP_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

(* a polynomial identity modulo the unit relation of the given hypothesis *)
let C981SPP_RING tm unit = SUBGOAL_THEN tm ASSUME_TAC THENL
  [UNDISCH_TAC unit THEN CONV_TAC REAL_RING; ALL_TAC];;

let C981SPP_UNFOLD_TAC t =
  MP_TAC(ASSUME t) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* normal bounds of all c977cc_normal assumptions, unfolded *)
let C981SPP_NORMALS_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns);;

let C981SPP_sqC = [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aC:real`];;
let C981SPP_sqB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`];;

(* r <= 5/7 from the normal bounds *)
let C981SPP_RBOUND_TAC =
  SUBGOAL_THEN `r <= &5 / &7` ASSUME_TAC THENL
   [C981SPP_CONTRA THEN
    C981SPP_PROD `&0 < (r - &5 / &7) * (r + &5 / &7)` THEN
    C981SPP_PROD `&0 <= (cC - &7 / &10) * (cC + &7 / &10)` THEN C981SPP_LIN;
    ALL_TAC];;

(* Lean: alternatives *)
let C981SPP_ALTERNATIVES = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ c977cc_normal cB sB /\ &0 < sB /\
     &1 < aC /\ aC = aB /\
     uC + aC <= (&47 / &20) * cC - (&33 / &20) * r /\
     linside cC sC uC vC aC (&2) (&2) /\
     linside cC sC uC vC aC (&2) (&3 / &2) /\
     linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> vC + aC <= ABT_lower cB sB uB vB aB r cC \/
         ABT_upper cC sC uC vC aC (--sB) cB <= vB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C981SPP_NORMALS_TAC THEN
  MP_TAC(CONV_RULE REAL_RAT_REDUCE_CONV
    (SPECL [`cC:real`; `--r:real`; `&7 / &10`; `--(&7 / &10)`] WFP_SHORT_PROJECTIONS)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABT_SB_TAC C981SPP_sqC `&2` `&2` `cC:real` `--r:real` THEN
  ABT_SB_TAC C981SPP_sqC `&2` `&2` `cB:real` `sB:real` THEN
  ABT_SB_TAC C981SPP_sqB `&33 / &20` `&47 / &20` `cC:real` `--r:real` THEN
  ABT_SB_TAC C981SPP_sqB `&33 / &20` `&47 / &20` `cB:real` `sB:real` THEN
  ABT_SB_TAC C981SPP_sqB `&33 / &20` `&47 / &20` `r:real` `cC:real` THEN
  ABT_SB_TAC C981SPP_sqB `&33 / &20` `&47 / &20` `--sB:real` `cB:real` THEN
  ABT_SB_TAC C981SPP_sqC `&33 / &20` `&33 / &20` `r:real` `cC:real` THEN
  ABT_SB_TAC C981SPP_sqC `&33 / &20` `&33 / &20` `--sB:real` `cB:real` THEN
  ABT_SB_TAC C981SPP_sqB `&1` `&12 / &5` `cB:real` `sB:real` THEN
  ABT_OWN_TAC C981SPP_sqC THEN ABT_OWN_TAC C981SPP_sqB THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cB` STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C981SPP_LIN; ALL_TAC] THEN
  MP_TAC(SPECL (C981SPP_sqC @ C981SPP_sqB) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG]) THEN
  (FIRST [MATCH_MP_TAC(TAUT `false ==> p`) THEN C981SPP_LIN;
          DISJ1_TAC THEN C981SPP_LIN;
          DISJ2_TAC THEN C981SPP_LIN;
          ALL_TAC]) THEN
  (* the remaining case: upper B (cB,sB) <= lower C (cB,sB) *)
  MP_TAC(SPECL [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aC:real`; `r:real`;
                `cB:real`; `sB:real`] C981SF_LOWER_NEGATIVE_POS) THEN
  C981SPP_PROD `&0 <= cB * (cC - r)` THEN
  C981SPP_PROD `&0 <= r * (cB - sB)` THEN
  C981SPP_PROD `&0 <= cB * r` THEN
  C981SPP_PROD `&0 < sB * cC` THEN
  ANTS_TAC THENL [REWRITE_TAC[] THEN CONJ_TAC THEN C981SPP_LIN; DISCH_TAC] THEN
  C981SPP_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&3 / &2)` THEN
  C981SPP_RBOUND_TAC THEN
  C981SPP_PROD `&0 <= (cB * cC - sB * r) * (((&47 / &20) * cC - (&33 / &20) * r - &1) - uC)` THEN
  C981SPP_PROD `&0 < (cB * r + sB * cC) * ((&2 * r + (&3 / &2) * cC) - vC)` THEN
  C981SPP_RING
   `(cB * cC - sB * r) * ((&47 / &20) * cC - (&33 / &20) * r - &1) +
    (cB * r + sB * cC) * (&2 * r + (&3 / &2) * cC) -
    ((&33 / &20) * cB + (&47 / &20) * sB) =
    cB * (&7 / &10 - cC - (&7 / &20) * r * r - (&3 / &20) * cC * r) +
    sB * (--(&17 / &20) + r + (&3 / &20) * r * r - (&7 / &20) * cC * r)`
   `cC * cC + --r * --r = &1` THEN
  C981SPP_PROD `&0 <= r * r` THEN
  C981SPP_PROD `&0 <= cC * r` THEN
  C981SPP_PROD `&0 <= r * (cC - r)` THEN
  C981SPP_PROD `&0 <= cB * --(&7 / &10 - cC - (&7 / &20) * r * r - (&3 / &20) * cC * r)` THEN
  C981SPP_PROD `&0 < sB * --(--(&17 / &20) + r + (&3 / &20) * r * r - (&7 / &20) * cC * r)` THEN
  MATCH_MP_TAC(TAUT `false ==> p`) THEN C981SPP_LIN);;

(* Lean: positive_v (private) *)
let C981SPP_POSITIVE_V = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ c977cc_normal cB sB /\ &1 < aB /\
     linside cC sC uC vC aC (&2) (&2) /\ linside cC sC uC vC aC (&3 / &2) (&2) /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     (vC + aC <= ABT_lower cB sB uB vB aB r cC \/
      ABT_upper cC sC uC vC aC (--sB) cB <= vB)
     ==> &3 * cB - (&3 / &2) * sB < vB + aB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --r`)) THEN
  C981SPP_NORMALS_TAC THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cB` STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C981SPP_LIN; ALL_TAC] THEN
  C981SPP_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&2)` THEN
  C981SPP_UNFOLD_TAC `linside cB sB uB vB aB (&1) (&113 / &50)` THEN
  C981SPP_CONTRA THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C981SPP_PROD `&0 <= cB * (cC - r)` THEN
    C981SPP_PROD `&0 <= r * (cB - sB)` THEN
    C981SPP_PROD `&0 <= cB * r` THEN
    C981SPP_PROD `&0 <= sB * cC` THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`; `cC:real`]
      C981NPR_LOWER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C981SPP_LIN; DISCH_TAC] THEN
    C981SPP_PROD `&0 <= (cB * r + sB * cC) * ((cB + (&113 / &50) * sB) - uB)` THEN
    C981SPP_PROD `&0 <= (cB * cC - sB * r) * ((&3 * cB - (&3 / &2) * sB - &1) - vB)` THEN
    C981SPP_PROD `&0 <= (&1 - cB) * (&3 * cB - &2)` THEN
    C981SPP_FACT `&1 - cB <= (&3 / &5) * sB * sB` THEN
    C981SPP_PROD `&0 <= sB * sB` THEN
    C981SPP_PROD `&0 <= cB * sB` THEN
    C981SPP_PROD `&0 <= sB * (cB - sB)` THEN
    C981SPP_FACT `&1 - cB - (&37 / &50) * sB * sB - cB * sB / &2 <= &0` THEN
    C981SPP_FACT `--(&1) + sB + sB * sB / &2 - (&37 / &50) * cB * sB <= &0` THEN
    C981SPP_PROD `&0 <= cC * --(&1 - cB - (&37 / &50) * sB * sB - cB * sB / &2)` THEN
    C981SPP_PROD `&0 <= r * --(--(&1) + sB + sB * sB / &2 - (&37 / &50) * cB * sB)` THEN
    C981SPP_RING
     `(cB * r + sB * cC) * (cB + (&113 / &50) * sB) +
      (cB * cC - sB * r) * (&3 * cB - (&3 / &2) * sB - &1) - &2 * (cC + r) =
      cC * (&1 - cB - (&37 / &50) * sB * sB - cB * sB / &2) +
      r * (--(&1) + sB + sB * sB / &2 - (&37 / &50) * cB * sB)`
     `cB * cB + sB * sB = &1` THEN
    C981SPP_LIN;
    ABT_SB_TAC [`cC:real`; `--r:real`; `uC:real`; `vC:real`; `aC:real`]
      `&3 / &2` `&2` `--sB:real` `cB:real` THEN
    C981SPP_LIN]);;

(* Lean: impossible *)
let C981SPP_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB r.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     sC = --r /\ c977cc_normal cC r /\ c977cc_normal cB sB /\
     &1 < aC /\ aC = aB /\
     &7 / &18 <= c981ha_half cB sB /\
     linside cC sC uC vC aC (&2) (&2) /\
     linside cC sC uC vC aC (&3 / &2) (&2) /\
     linside cC sC uC vC aC (&2) (&3 / &2) /\
     linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     ~linside cC sC uC vC aC (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&3 / &2) (&3) /\
     ~linside cB sB uB vB aB (&1) (&3) /\
     ldisj cC sC uC vC aC cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < sB` ASSUME_TAC THENL
   [C981SPP_CONTRA THEN
    SUBGOAL_THEN `sB = &0` SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[c977cc_normal] o
        check (fun th -> concl th = `c977cc_normal cB sB`)) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `&7 / &18 <= c981ha_half cB (&0)` THEN
    REWRITE_TAC[c981ha_half; real_div; REAL_MUL_LZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `r:real`]
    C981NPR_CENTRAL_CAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`]
    C981SPP_ALTERNATIVES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`]
    C981SPP_POSITIVE_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[REAL_LT_TRANS]; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sC:real = --r`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aB`)) THEN
  C981SPP_NORMALS_TAC THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cB` STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C981SPP_LIN; ALL_TAC] THEN
  C981SPP_UNFOLD_TAC `linside cB sB uB vB aC (&33 / &20) (&47 / &20)` THEN
  C981SPP_UNFOLD_TAC `linside cB sB uB vB aC (&1) (&113 / &50)` THEN
  C981SPP_UNFOLD_TAC `linside cB sB uB vB aC (&1) (&12 / &5)` THEN
  C981SPP_UNFOLD_TAC `linside cC (--r) uC vC aC (&2) (&2)` THEN
  SUBGOAL_THEN `uB + aC <= (&3 / &2) * cB + &3 * sB` ASSUME_TAC THENL
   [C981SPP_CONTRA THEN UNDISCH_TAC `~linside cB sB uB vB aC (&3 / &2) (&3)` THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981SPP_LIN;
    ALL_TAC] THEN
  SUBGOAL_THEN `vB + aC <= &3 * cB - sB` ASSUME_TAC THENL
   [C981SPP_CONTRA THEN UNDISCH_TAC `~linside cB sB uB vB aC (&1) (&3)` THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C981SPP_LIN;
    ALL_TAC] THEN
  C981SPP_PROD `&0 <= cB * (cC - r)` THEN
  C981SPP_PROD `&0 <= r * (cB - sB)` THEN
  C981SPP_PROD `&0 <= cB * r` THEN
  C981SPP_PROD `&0 < sB * cC` THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C981SPP_PROD `&0 <= (cB + sB - &1) * (&10 / &7 - (cB + sB))` THEN
    C981SPP_PROD `&0 < cB * sB` THEN
    C981SPP_FACT `&0 < cB + sB - &1 - cB * sB / &2` THEN
    C981SPP_PROD `&0 <= sB * sB` THEN
    C981SPP_FACT `sB - cB - &1 / &2 - sB * sB / &2 <= &0` THEN
    C981SPP_PROD `&0 < cC * (cB + sB - &1 - cB * sB / &2)` THEN
    C981SPP_PROD `&0 <= r * --(sB - cB - &1 / &2 - sB * sB / &2)` THEN
    C981SPP_PROD `&0 <= (cB * r + sB * cC) * (((&3 / &2) * cB + &3 * sB - &1) - uB)` THEN
    C981SPP_PROD `&0 <= (cB * cC - sB * r) * ((&3 * cB - sB - &1) - vB)` THEN
    C981SPP_RING
     `(cB * r + sB * cC) * ((&3 / &2) * cB + &3 * sB - &1) +
      (cB * cC - sB * r) * (&3 * cB - sB - &1) - &2 * (cC + r) =
      --cC * (cB + sB - &1 - cB * sB / &2) + r * (sB - cB - &1 / &2 - sB * sB / &2)`
     `cB * cB + sB * sB = &1` THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aC:real`; `r:real`; `cC:real`]
      C981NPR_LOWER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C981SPP_LIN; DISCH_TAC] THEN
    C981SPP_LIN;
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
      (CONJ_TAC THENL [C981SPP_LIN; REAL_ARITH_TAC]);
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  C981SPP_PROD `&0 <= (cB * r + sB * cC) * ((&7 / &20) * (cC + r) - (uC + aC - &2 * (cC - r)))` THEN
  C981SPP_PROD `&0 <= (cB * cC - sB * r) * (vC + aC - &2 * (cC + r))` THEN
  C981SPP_PROD `&0 < (aC - &1) * (&1 + (cB * r + sB * cC))` THEN
  C981SPP_RING
   `--(cB * r + sB * cC) * uC + (cB * cC - sB * r) * (vC + aC) =
    &2 * (cB - sB) + aC * (cB * r + sB * cC) -
    (cB * r + sB * cC) * (uC + aC - &2 * (cC - r)) +
    (cB * cC - sB * r) * (vC + aC - &2 * (cC + r))`
   `cC * cC + --r * --r = &1` THEN
  MP_TAC(SPECL [`cC:real`; `r:real`; `cB:real`; `sB:real`] C981AS_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN C981SPP_LIN);;

(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallLeftResidual.lean (Jatloe,           *)
(* N12-jatloe; namespace N12Compact.FullAuxWallLeftResidual).                *)
(* Necessary angle inequalities from the genuine left wall and positive      *)
(* upper central square.  Normal is c977cc_normal; upper/lower are ABT_upper/*)
(* ABT_lower; lower_pp: FAWTE_LOWER_PP; the four-axis split is ABT_FOUR_AXES;*)
(* K and Q are fawlr_k and fawlr_q.  L.s = -r is sL = --r.                   *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallPositiveTop.ml";;

let FAWLR_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWLR_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let FAWLR_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
         CONV_TAC REAL_RING];;

let FAWLR_SB_TAC sq (x,y) (nx,ny) =
  MP_TAC(REWRITE_RULE[REAL_POW_2] (SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS)) THEN
  ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC];;

(* Lean: K (definition) *)
let fawlr_k = new_definition
 `fawlr_k (b:real) t = b + t - &1 - (&3 / &5) * b * t`;;

(* Lean: Q (definition) *)
let fawlr_q = new_definition
 `fawlr_q (b:real) t = t - b + (&343 / &500) - (&3 / &5) * t pow 2`;;

(* Lean: coefficient_signs *)
let FAWLR_COEFFICIENT_SIGNS = prove
 (`forall b t. c977cc_normal b t /\ &1 < (&343 / &500) * b + t
     ==> &0 <= fawlr_k b t /\ &0 < fawlr_q b t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWLR_NORMAL_TAC THEN
  REWRITE_TAC[fawlr_k; fawlr_q] THEN
  FAWLR_PROD_TAC `b + t - &1` `&3 / &2 - (b + t)` THEN
  SUBGOAL_THEN `(&4 / &5) * b * t <= b + t - &1` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWLR_PROD_TAC `b:real` `t:real` THEN
  SUBGOAL_THEN `t pow 2 / &2 <= &1 - b` ASSUME_TAC THENL
  [NLIN_TAC [SQ_NONNEG `b - &1`]; ALL_TAC] THEN
  CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `t:real`]);;

(* Lean: no_upper_v *)
let FAWLR_NO_UPPER_V = prove
 (`forall cL sL uL vL aL cB sB uB vB aB.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cB sB /\ &1 < aB /\ vB + aB <= &3 * cB - sB /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\ linside cL sL uL vL aL (&1) (&8 / &5) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     (ABT_upper cL sL uL vL aL (--sB) cB <= ABT_lower cB sB uB vB aB (--sB) cB \/
      ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cL sL uL vL aL (--sB) cB)
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FAWLR_NORMAL_TAC THEN
  let qL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
  and qB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] in
  FAWLR_SB_TAC qL (`&457 / &500`,`&2`) (`--sB`,`cB:real`) THEN
  FAWLR_SB_TAC qL (`&1`,`&8 / &5`) (`--sB`,`cB:real`) THEN
  FAWLR_SB_TAC qB (`&1`,`&12 / &5`) (`--sB`,`cB:real`) THEN
  MP_TAC(SPECL qB ABT_OWNV) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN RASM_ARITH_TAC);;

(* Lean: positive_v_order *)
let FAWLR_POSITIVE_V_ORDER = prove
 (`forall cL sL uL vL aL cB sB uB vB aB.
     c977cc_normal cL sL /\ c977cc_normal cB sB /\ &1 < aB /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     &1 < (&343 / &500) * cB + sB /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     vL + aL <= ABT_lower cB sB uB vB aB (--sL) cL
     ==> cL * sB < sL * cB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWLR_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FAWLR_PROD_TAC `cL:real` `cB:real` THEN FAWLR_PROD_TAC `sL:real` `sB:real` THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `--sL`; `cL:real`]
    FAWTE_LOWER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aB (--sL) cL =
                (cL * sB - sL * cB) * uB + (cL * cB + sL * sB) * vB` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  FAWLR_PROD_TAC `cL * sB - sL * cB` `(&8 / &5) * cB + &3 * sB - &1 - uB` THEN
  FAWLR_PROD_TAC `cL * cB + sL * sB` `&3 * cB - sB - &1 - vB` THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`] FAWLR_COEFFICIENT_SIGNS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FAWLR_PROD_TAC `cL:real` `fawlr_k cB sB` THEN FAWLR_PROD_TAC `sL:real` `fawlr_q cB sB` THEN
  SUBGOAL_THEN
   `(cL * sB - sL * cB) * ((&8 / &5) * cB + &3 * sB - &1) +
    (cL * cB + sL * sB) * (&3 * cB - sB - &1) - (&2 * cL - (&457 / &500) * sL) =
    --cL * fawlr_k cB sB - sL * fawlr_q cB sB` ASSUME_TAC THENL
  [REWRITE_TAC[fawlr_k; fawlr_q] THEN UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cL sL uL vL aL (&457 / &500) (&2)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: negative_v_order *)
let FAWLR_NEGATIVE_V_ORDER = prove
 (`forall cL sL uL vL aL cB sB uB vB aB r.
     sL = --r /\ c977cc_normal cL r /\ c977cc_normal cB sB /\ &1 < aB /\
     uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     vL + aL <= ABT_lower cB sB uB vB aB r cL
     ==> cL * fawlr_k cB sB < r * fawlr_q cB sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sL = --r`)) THEN
  FAWLR_NORMAL_TAC THEN
  FAWLR_PROD_TAC `r:real` `cB:real` THEN FAWLR_PROD_TAC `cL:real` `sB:real` THEN
  FAWLR_PROD_TAC `cB:real` `cL - r` THEN FAWLR_PROD_TAC `r:real` `cB - sB` THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `r:real`; `cL:real`]
    FAWTE_LOWER_PP) THEN
  ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
  SUBGOAL_THEN `ABT_lower cB sB uB vB aB r cL =
                (r * cB + cL * sB) * uB + (cL * cB - r * sB) * vB` ASSUME_TAC THENL
  [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= cL * cB - r * sB` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  FAWLR_PROD_TAC `r * cB + cL * sB` `(&8 / &5) * cB + &3 * sB - &1 - uB` THEN
  FAWLR_PROD_TAC `cL * cB - r * sB` `&3 * cB - sB - &1 - vB` THEN
  SUBGOAL_THEN
   `(r * cB + cL * sB) * ((&8 / &5) * cB + &3 * sB - &1) +
    (cL * cB - r * sB) * (&3 * cB - sB - &1) - (&2 * cL + (&457 / &500) * r) =
    --cL * fawlr_k cB sB + r * fawlr_q cB sB` ASSUME_TAC THENL
  [REWRITE_TAC[fawlr_k; fawlr_q] THEN UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN
   CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(ASSUME `linside cL (--r) uL vL aL (&457 / &500) (&2)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: no_opposite_v *)
let FAWLR_NO_OPPOSITE_V = prove
 (`forall cL sL uL vL aL cD sD uD vD aD.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cD sD /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\ linside cL sL uL vL aL (&1) (&8 / &5) /\
     linside cD sD uD vD aD (&2) (&3 / &2) /\ linside cD sD uD vD aD (&6 / &5) (&19 / &10) /\
     (ABT_upper cL sL uL vL aL (--sD) cD <= ABT_lower cD sD uD vD aD (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sD) cD <= ABT_lower cL sL uL vL aL (--sD) cD)
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FAWLR_NORMAL_TAC THEN
  let qL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
  and qD = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] in
  FAWLR_SB_TAC qL (`&457 / &500`,`&2`) (`--sD`,`cD:real`) THEN
  FAWLR_SB_TAC qL (`&1`,`&8 / &5`) (`--sD`,`cD:real`) THEN
  FAWLR_SB_TAC qD (`&2`,`&3 / &2`) (`--sD`,`cD:real`) THEN
  FAWLR_SB_TAC qD (`&6 / &5`,`&19 / &10`) (`--sD`,`cD:real`) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN RASM_ARITH_TAC);;

(* Lean: positive_left_axes *)
let FAWLR_POSITIVE_LEFT_AXES = prove
 (`forall cL sL uL vL aL cD sD uD vD aD.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     c977cc_normal cL sL /\ c977cc_normal cD sD /\ aL = aD /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\ linside cL sL uL vL aL (&1) (&8 / &5) /\
     linside cD sD uD vD aD (&2) (&2) /\ linside cD sD uD vD aD (&2) (&3 / &2) /\
     linside cD sD uD vD aD (&6 / &5) (&19 / &10) /\
     ldisj cL sL uL vL aL cD sD uD vD aD
     ==> uL + aL <= ABT_lower cD sD uD vD aD cL sL \/
         ABT_upper cL sL uL vL aL cD sD <= uD`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWLR_NORMAL_TAC THEN
  let qL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`]
  and qD = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`] in
  let mk = (`&457 / &500`,`&2`) and lo = (`&1`,`&8 / &5`) and ce = (`&2`,`&2`)
  and bo = (`&2`,`&3 / &2`) and le = (`&6 / &5`,`&19 / &10`) in
  let d1 = (`cL:real`,`sL:real`) and d2 = (`--sL`,`cL:real`)
  and d3 = (`cD:real`,`sD:real`) and d4 = (`--sD`,`cD:real`) in
  MAP_EVERY (fun (sq,p,d) -> FAWLR_SB_TAC sq p d)
   [qD,ce,d1; qL,mk,d1; qD,ce,d3; qL,mk,d3;
    qL,mk,d2; qD,bo,d2; qD,le,d2; qL,lo,d2;
    qL,mk,d4; qD,bo,d4; qD,le,d4; qL,lo,d4] THEN
  MP_TAC(SPECL (qL @ qD) ABT_FOUR_AXES) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL qL ABT_OWNU) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL qD ABT_OWNU) THEN ANTS_TAC THENL [FAWLR_ANTS_TAC; STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RASM_ARITH_TAC);;

(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveTop.lean (Jatloe, N12-jatloe; *)
(* namespace N12Compact.FullAuxWallPositiveTop).  Genuine upper and lower    *)
(* faces of the positive outer square.  Normal is c977cc_normal; upper/lower *)
(* are ABT_upper/ABT_lower; lower_pp / lower_np: FAWTE_LOWER_PP / ..NP;      *)
(* FullAuxWallPositiveTopMargins.c_axis_above / c_axis_below / b_axis_above: *)
(* FAWPTM_..; FullAuxWallPositiveEndpointMargin.shallow_margin:              *)
(* FAWPEM_SHALLOW_MARGIN.  The OpenSquare invariants are explicit.           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/CP_C981_NegativePoint.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallPositiveEndpointMargin.ml";;
needs "n12/geometry/FullAuxWallPositiveTopMargins.ml";;
needs "n12/geometry/FullAuxWallPositiveTransverse.ml";;

let FAWPTP_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPTP_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let FAWPTP_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: upper_pp (private) *)
let FAWPTP_UPPER_PP = prove
 (`forall c s u v a x y. &0 <= x * c + y * s /\ &0 <= --x * s + y * c
     ==> ABT_upper c s u v a x y =
         (x * c + y * s) * (u + a) + (--x * s + y * c) * (v + a)`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

(* Lean: upper_np (private) *)
let FAWPTP_UPPER_NP = prove
 (`forall c s u v a x y. x * c + y * s <= &0 /\ &0 <= --x * s + y * c
     ==> ABT_upper c s u v a x y = (x * c + y * s) * u + (--x * s + y * c) * (v + a)`,
  REPEAT STRIP_TAC THEN C981NP_FORM_TAC);;

let FAWPTP_FORM_TAC th sq nx ny =
  MP_TAC(SPECL (sq @ [nx; ny]) th) THEN
  ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
  FIRST_X_ASSUM(fun eq -> RULE_ASSUM_TAC(REWRITE_RULE[eq]) THEN
    ASSUME_TAC eq);;

(* Lean: endpoint_v *)
let FAWPTP_ENDPOINT_V = prove
 (`forall cD sD uD vD aD cB sB uB vB aB.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cD sD /\ c977cc_normal cB sB /\ &1 < aD /\ &1 < aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     uD + aD - &2 * (cD + sD) < &1 / &10 /\
     cD - (&8 / &5) * sD <= vD /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB)
     ==> &3 * cB - (&8 / &5) * sB < vB + aB`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN FAWPTP_NORMAL_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cD sD uD vD aD (&2) (&2)`; `linside cB sB uB vB aB (&1) (&113 / &50)`;
    `linside cB sB uB vB aB (&33 / &20) (&47 / &20)`] THEN
  FAWPTP_PROD_TAC `cD:real` `cB:real` THEN FAWPTP_PROD_TAC `sD:real` `sB:real` THEN
  FAWPTP_PRODLT_TAC `cD:real` `cB:real` THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  let qD = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`]
  and qB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] in
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [FAWPTP_PROD_TAC `cD * cB + sD * sB` `(&3 * cB - (&8 / &5) * sB - &1) - vB` THEN
   ASM_CASES_TAC `&0 <= cD * sB - sD * cB` THENL
   [FAWPTP_FORM_TAC FAWTE_LOWER_PP qB `--sD` `cD:real` THEN
    FAWPTP_PROD_TAC `cD * sB - sD * cB` `(cB * &1 + sB * &113 / &50) - uB` THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `sB:real`] FAWPTM_C_AXIS_ABOVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(cD * sB - sD * cB) * (cB + (&113 / &50) * sB) +
      (cD * cB + sD * sB) * (&3 * cB - (&8 / &5) * sB - &1) - (cD - (&8 / &5) * sD) =
      cD * (&2 - cB - (&37 / &50) * sB pow 2 - (&3 / &5) * cB * sB) +
      sD * ((&3 / &5) - (&3 / &5) * sB pow 2 + (&37 / &50) * cB * sB - sB)` ASSUME_TAC THENL
    [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    FAWPTP_FORM_TAC FAWTE_LOWER_NP qB `--sD` `cD:real` THEN
    FAWPTP_PROD_TAC `--(cD * sB - sD * cB)`
      `(uB + aB) - (cB * &33 / &20 + sB * &47 / &20)` THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `sB:real`] FAWPTM_C_AXIS_BELOW) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(cD * sB - sD * cB) * ((&33 / &20) * cB + (&47 / &20) * sB) +
      (cD * cB + sD * sB) * (&3 * cB - (&8 / &5) * sB - &1) - (cD - (&8 / &5) * sD) =
      cD * (&2 - cB - (&13 / &20) * sB pow 2 + (&1 / &20) * cB * sB) +
      sD * (--(&1 / &20) + (&1 / &20) * sB pow 2 + (&13 / &20) * cB * sB - sB)`
     ASSUME_TAC THENL
    [UNDISCH_TAC `cB pow 2 + sB pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_TAC ~deg2:false []];
   FAWPTP_PRODLT_TAC `cD * cB + sD * sB` `(vD + aD) - (&1 + cD - (&8 / &5) * sD)` THEN
   ASM_CASES_TAC `&0 <= cD * sB - sD * cB` THENL
   [FAWPTP_FORM_TAC FAWPTP_UPPER_NP qD `--sB` `cB:real` THEN
    FAWPTP_PROD_TAC `cD * sB - sD * cB` `(&2 * (cD + sD) - &9 / &10) - uD` THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `sB:real`] FAWPTM_B_AXIS_ABOVE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&1 - (cD * sB - sD * cB) * (&2 * (cD + sD) - &9 / &10) +
      (cD * cB + sD * sB) * (&1 + cD - (&8 / &5) * sD) - (&3 * cB - (&8 / &5) * sB) =
      &1 + cB * (cD - &2 + sD pow 2 + (&2 / &5) * cD * sD - (&9 / &10) * sD) +
      sB * (sD - cD * sD - (&2 / &5) * cD pow 2 + (&9 / &10) * cD)` ASSUME_TAC THENL
    [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    FAWPTP_FORM_TAC FAWPTP_UPPER_PP qD `--sB` `cB:real` THEN
    FAWPTP_PROD_TAC `--(cD * sB - sD * cB)` `(uD + aD) - &2 * (cD + sD)` THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `sB:real`] FAWPEM_SHALLOW_MARGIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&1 - (cD * sB - sD * cB) * (&2 * (cD + sD)) +
      (cD * cB + sD * sB) * (&1 + cD - (&8 / &5) * sD) - (&3 * cB - (&8 / &5) * sB) =
      &1 - cB * (&1 - cD + cD pow 2 - (&2 / &5) * cD * sD) +
      sB * (sD * (&1 - cD) - (&2 / &5) * cD pow 2)` ASSUME_TAC THENL
    [UNDISCH_TAC `cD pow 2 + sD pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_TAC ~deg2:false []]]);;

(* Lean: corner_marker_faces *)
let FAWPTP_CORNER_MARKER_FACES = prove
 (`forall c s u v a.
     c977cc_normal c s /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&3) /\ ~linside c s u v a (&457 / &500) (&2)
     ==> v + a <= &3 * c - s /\ (&457 / &500) * c + &2 * s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPTP_NORMAL_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside c s u v a (&33 / &20) (&47 / &20)`; `linside c s u v a (&1) (&12 / &5)`] THEN
  SUBGOAL_THEN `v + a <= &3 * c - s` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside c s u v a (&1) (&3)` THEN REWRITE_TAC[linside] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~linside c s u v a (&457 / &500) (&2)` THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* Lean: faces *)
let FAWPTP_FACES = prove
 (`forall cD sD uD vD aD cB sB uB vB aB.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cD sD /\ c977cc_normal cB sB /\ &1 < aD /\ &1 < aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     uD + aD - &2 * (cD + sD) < &1 / &10 /\
     cD - (&8 / &5) * sD <= vD /\
     linside cB sB uB vB aB (&1) (&113 / &50) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB) /\
     ~linside cB sB uB vB aB (&8 / &5) (&3) /\
     ~linside cB sB uB vB aB (&1) (&3) /\
     ~linside cB sB uB vB aB (&457 / &500) (&2)
     ==> uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
         (&457 / &500) * cB + &2 * sB <= uB /\ &3 / &10 < sB`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] FAWPTP_ENDPOINT_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    FAWPTP_CORNER_MARKER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FAWPTP_NORMAL_TAC THEN
  MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t)))
   [`linside cB sB uB vB aB (&33 / &20) (&47 / &20)`;
    `linside cB sB uB vB aB (&1) (&12 / &5)`] THEN
  SUBGOAL_THEN `uB + aB <= (&8 / &5) * cB + &3 * sB` ASSUME_TAC THENL
  [UNDISCH_TAC `~linside cB sB uB vB aB (&8 / &5) (&3)` THEN REWRITE_TAC[linside] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

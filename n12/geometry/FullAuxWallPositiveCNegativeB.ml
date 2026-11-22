(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveCNegativeB.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveCNegativeB).          *)
(* The positive opposite square and negative upper central square.           *)
(* Normal is c977cc_normal; lower/upper are ABT_lower/ABT_upper; B.s = -t is *)
(* sB = --t.  lower_np: FAWTE_LOWER_NP; FullAuxWallPositiveCNegativeB-       *)
(* Margins.lower_u / upper_v: FAWPCNB_LOWER_U / FAWPCNB_UPPER_V;             *)
(* FullAuxWallPositiveOpposite.alternatives / upper_u_offset: FAWPO_..;      *)
(* FullAuxWallPositiveReach.bottom_u / bottom_face / point: FAWPR_..;        *)
(* FullAuxWallPositiveTransverse.alternatives: FAWPT_ALTERNATIVES.           *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallTopEndpoint.ml";;
needs "n12/geometry/FullAuxWallPositiveCNegativeBMargins.ml";;
needs "n12/geometry/FullAuxWallPositiveOpposite.ml";;
needs "n12/geometry/FullAuxWallPositiveReach.ml";;
needs "n12/geometry/FullAuxWallPositiveTransverse.ml";;

let FAWPCN_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPCN_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let FAWPCN_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
         CONV_TAC REAL_RING];;

(* Lean: endpoint_cap *)
let FAWPCN_ENDPOINT_CAP = prove
 (`forall c s u v a t.
     s = --t /\ c977cc_normal c t /\
     linside c s u v a (&33 / &20) (&47 / &20) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&8 / &5) (&3)
     ==> v + a <= &3 * c + (&8 / &5) * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  FAWPCN_NORMAL_TAC THEN
  MP_TAC(ASSUME `linside c (--t) u v a (&33 / &20) (&47 / &20)`) THEN
  MP_TAC(ASSUME `linside c (--t) u v a (&1) (&12 / &5)`) THEN
  MP_TAC(ASSUME `~linside c (--t) u v a (&8 / &5) (&3)`) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: corner_faces *)
let FAWPCN_CORNER_FACES = prove
 (`forall c s u v a t.
     s = --t /\ c977cc_normal c t /\
     linside c s u v a (&33 / &20) (&47 / &20) /\ ~linside c s u v a (&1) (&3)
     ==> c - &3 * t <= u \/ v + a <= &3 * c + t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  FAWPCN_NORMAL_TAC THEN
  MP_TAC(ASSUME `linside c (--t) u v a (&33 / &20) (&47 / &20)`) THEN
  MP_TAC(ASSUME `~linside c (--t) u v a (&1) (&3)`) THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: impossible_of_transverse *)
let FAWPCN_IMPOSSIBLE_OF_TRANSVERSE = prove
 (`forall cD sD uD vD aD cB sB uB vB aB t.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cD sD /\ sB = --t /\ c977cc_normal cB t /\
     &1 < aD /\ &1 < aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     cD - (&8 / &5) * sD <= vD /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&8 / &5) (&3) /\ ~linside cB sB uB vB aB (&1) (&3) /\
     (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
      ABT_upper cD sD uD vD aD (--sB) cB <= vB)
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`]
    FAWPCN_ENDPOINT_CAP) THEN
  ANTS_TAC THENL [FAWPCN_ANTS_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`]
    FAWPCN_CORNER_FACES) THEN
  ANTS_TAC THENL [FAWPCN_ANTS_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `sB = --t`)) THEN
  FAWPCN_NORMAL_TAC THEN
  MP_TAC(ASSUME `linside cB (--t) uB vB aB (&33 / &20) (&47 / &20)`) THEN
  REWRITE_TAC[linside] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term (fun t -> t = `vB:real`)) (concl th) &&
    can (find_term (fun t -> t = `vD:real`)) (concl th))) THENL
  [FAWPCN_PROD_TAC `cB:real` `sD:real` THEN FAWPCN_PROD_TAC `t:real` `cD:real` THEN
   FAWPCN_PROD_TAC `cB:real` `cD - sD` THEN FAWPCN_PROD_TAC `sD:real` `cB - t` THEN
   MP_TAC(SPECL [`cB:real`; `--t`; `uB:real`; `vB:real`; `aB:real`; `--sD`; `cD:real`]
     FAWTE_LOWER_NP) THEN
   ANTS_TAC THENL [CONJ_TAC THEN NLIN_TAC ~deg2:false []; DISCH_TAC] THEN
   SUBGOAL_THEN `ABT_lower cB (--t) uB vB aB (--sD) cD =
                 --(cB * sD + t * cD) * (uB + aB) + (cB * cD - t * sD) * vB` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[ASSUME `ABT_lower cB (--t) uB vB aB (--sD) cD =
                 --(cB * sD + t * cD) * (uB + aB) + (cB * cD - t * sD) * vB`]) THEN
   SUBGOAL_THEN `&0 <= cB * sD + t * cD /\ &0 <= cB * cD - t * sD` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [FAWPCN_PROD_TAC `cB * sD + t * cD` `uB + aB - (&1 + cB - &3 * t)` THEN
    FAWPCN_PROD_TAC `cB * cD - t * sD` `&3 * cB + (&8 / &5) * t - &1 - vB` THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `t:real`] FAWPCNB_LOWER_U) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `--(cB * sD + t * cD) * (&1 + cB - &3 * t) + (cB * cD - t * sD) * (&3 * cB + (&8 / &5) * t - &1) -
      (&1 + cD - (&8 / &5) * sD) =
      cD * (&2 - cB - t + (&3 / &5) * cB * t) +
      sD * ((&3 / &5) - cB + t - (&3 / &5) * t pow 2) - &1` ASSUME_TAC THENL
    [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_TAC ~deg2:false [];
    FAWPCN_PROD_TAC `cB * sD + t * cD` `uB + aB - ((&33 / &20) * cB - (&47 / &20) * t)` THEN
    FAWPCN_PROD_TAC `cB * cD - t * sD` `&3 * cB + t - &1 - vB` THEN
    MP_TAC(SPECL [`cD:real`; `sD:real`; `cB:real`; `t:real`] FAWPCNB_UPPER_V) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `--(cB * sD + t * cD) * ((&33 / &20) * cB - (&47 / &20) * t) +
      (cB * cD - t * sD) * (&3 * cB + t - &1) - (&1 + cD - (&8 / &5) * sD) =
      cD * (&2 - cB - (&13 / &20) * t pow 2 - (&13 / &20) * cB * t) +
      sD * (--(&1 / &20) + (&13 / &20) * t pow 2 - (&13 / &20) * cB * t + t) - &1`
     ASSUME_TAC THENL
    [UNDISCH_TAC `cB pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
    NLIN_TAC ~deg2:false []];
   MP_TAC(REWRITE_RULE[REAL_NEG_NEG] (SPECL [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`;
     `&2`; `&2`; `--(--t)`; `cB:real`] ABT_STRICT_BOUNDS)) THEN
   ANTS_TAC THENL [FAWPCN_ANTS_TAC; STRIP_TAC] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_NEG_NEG]) THEN
   RASM_ARITH_TAC]);;

(* Lean: impossible *)
let FAWPCN_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cD sD uD vD aD cB sB uB vB aB t.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cD * cD + sD * sD = &1 /\ &0 < aD /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cA sA /\ c977cc_normal cD sD /\ sB = --t /\ c977cc_normal cB t /\
     &1 < aA /\ aA = aD /\ aD = aB /\
     &0 < sA /\ &4 * sA <= cA /\ &2 * (cA + sA) <= uA /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&5 / &2) (&3) /\
     vA + aA <= &3 * cA - (&12 / &5) * sA /\
     linside cD sD uD vD aD (&2) (&2) /\
     linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
     linside cD sD uD vD aD (&2) (&3 / &2) /\
     ~linside cD sD uD vD aD (&8 / &5) (&1) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ~linside cB sB uB vB aB (&8 / &5) (&3) /\ ~linside cB sB uB vB aB (&1) (&3) /\
     ldisj cA sA uA vA aA cD sD uD vD aD /\
     ldisj cD sD uD vD aD cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN FAWPCN_NORMAL_TAC THEN
  let qA = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
  and qD = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`]
  and qB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] in
  let use th tms = MP_TAC(SPECL tms th) THEN ANTS_TAC THENL [FAWPCN_ANTS_TAC; DISCH_TAC] in
  use FAWPO_ALTERNATIVES (qA @ qD) THEN
  use FAWPO_UPPER_U_OFFSET (qA @ qD) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  use FAWPR_BOTTOM_U (qA @ qD) THEN
  use FAWPR_BOTTOM_FACE qD THEN
  use FAWPR_POINT qD THEN
  use FAWPT_ALTERNATIVES (qD @ qB) THEN
  MATCH_MP_TAC(SPECL (qD @ qB @ [`t:real`]) FAWPCN_IMPOSSIBLE_OF_TRANSVERSE) THEN
  FAWPCN_ANTS_TAC);;

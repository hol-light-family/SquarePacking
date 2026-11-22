(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveTransverse.lean (Jatloe,      *)
(* N12-jatloe; namespace N12Compact.FullAuxWallPositiveTransverse).          *)
(* The SAT reduction shared by all signed outer-square frames.  Normal is    *)
(* c977cc_normal; upper/lower are ABT_upper/ABT_lower; the four-axis split   *)
(* (CongruentSAT.faceSeparation_of_disjoint) is ABT_FOUR_AXES.               *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallPositiveReach.ml";;

let FAWPT_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let FAWPT_ANTS_TAC =
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC;
         POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o
           filter (fun th -> is_eq(concl th) && type_of(lhs(concl th)) = `:real`)) THEN
         CONV_TAC REAL_RING];;

(* Lean: alternatives *)
let FAWPT_ALTERNATIVES = prove
 (`forall cD sD uD vD aD cB sB uB vB aB.
     cD * cD + sD * sD = &1 /\ &0 < aD /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     c977cc_normal cD sD /\ &0 < cB /\ --cB <= sB /\ sB <= cB /\ aD = aB /\
     linside cD sD uD vD aD (&2) (&2) /\
     linside cD sD uD vD aD (&6 / &5) (&19 / &10) /\
     linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&1) (&12 / &5) /\
     ldisj cD sD uD vD aD cB sB uB vB aB
     ==> vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
         ABT_upper cD sD uD vD aD (--sB) cB <= vB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aD:real = aB`)) THEN
  FAWPT_NORMAL_TAC THEN
  let qD = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`]
  and qB = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aD:real`] in
  let sb sq (x,y) (nx,ny) =
    MP_TAC(REWRITE_RULE[REAL_POW_2] (SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS)) THEN
    ANTS_TAC THENL [FAWPT_ANTS_TAC; STRIP_TAC] in
  let d1 = (`cD:real`,`sD:real`) and d2 = (`--sD`,`cD:real`)
  and d3 = (`cB:real`,`sB:real`) and d4 = (`--sB`,`cB:real`) in
  let ce = (`&2`,`&2`) and le = (`&6 / &5`,`&19 / &10`) and sw = (`&33 / &20`,`&33 / &20`)
  and mk = (`&33 / &20`,`&47 / &20`) and hi = (`&1`,`&12 / &5`) in
  MAP_EVERY (fun (sq,p,d) -> sb sq p d)
   [qD,ce,d1; qD,le,d1; qB,mk,d1; qD,ce,d3; qD,le,d3; qB,mk,d3; qB,hi,d3;
    qD,sw,d2; qB,mk,d2; qD,sw,d4; qB,mk,d4] THEN
  MP_TAC(SPECL (qD @ qB) ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [FAWPT_ANTS_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL qD ABT_OWNV) THEN ANTS_TAC THENL [FAWPT_ANTS_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL qB ABT_OWNV) THEN ANTS_TAC THENL [FAWPT_ANTS_TAC; STRIP_TAC] THEN
  REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl))) THEN
  RASM_ARITH_TAC);;

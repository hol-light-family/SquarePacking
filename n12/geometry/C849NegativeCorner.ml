(* ========================================================================= *)
(* Port of Compact/Geometry/C849NegativeCorner.lean                          *)
(*                                                                           *)
(* Squares B = (cB,sB,uB,vB,aB) and E = (cE,sE,uE,vE,aE).                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CornerInwardPoint.ml";;

(* Lean: lower_face *)
let C849NC_LOWER_FACE = prove
 (`forall cB sB uB vB aB cE sE uE vE aE.
     cB * cB + sB * sB = &1 /\ cE * cE + sE * sE = &1 /\
     &0 < cB /\ sB <= &0 /\ --sB <= cB /\
     aE = aB /\ &1 < aB /\ aB <= &1001 / &1000 /\ lcont cE sE uE vE aE /\
     linside cE sE uE vE aE (&1) (&1543 / &500) /\
     linside cE sE uE vE aE (&457 / &500) (&3) /\
     linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     ldisj cB sB uB vB aB cE sE uE vE aE
     ==> aB * (cB - sB) + &4 * sB <= uB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    CIP_OUTSIDE_UPPER_LEFT) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aE:real = aB`)) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; lclosed]) THEN REWRITE_TAC[linside] THEN
  DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th))) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN NLIN_TAC []);;

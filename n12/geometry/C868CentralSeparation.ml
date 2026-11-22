(* ========================================================================= *)
(* Port of Compact/Geometry/C868CentralSeparation.lean (Jatloe, N12-jatloe).  *)
(* Exact separating-axis reduction for the lower-left square A and the upper *)
(* central pair H.  upper / lower: ABT_upper / ABT_lower; the SAT reduction  *)
(* (faceSeparation_of_disjoint, separated, parallel/transverse_radius,       *)
(* ownU/ownV) is ABT_PAIR_TAC.  Normal: c977cc_normal.                       *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C868CentralSupport.ml";;

(* Lean: alternatives *)
let C868CSEP_ALTERNATIVES = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     &0 < cA /\ --cA <= sA /\ sA <= cA /\
     &0 < cH /\ --cH <= sH /\ sH <= cH /\
     aA = aH /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     (&33 / &20) * cA + (&47 / &20) * sA < ABT_upper cA sA uA vA aA cA sA /\
     (&33 / &20) * cH + (&47 / &20) * sH < ABT_upper cA sA uA vA aA cH sH /\
     ldisj cA sA uA vA aA cH sH uH vH aH
     ==> ABT_upper cA sA uA vA aA (--sH) cH <= vH \/
         vA + aA <= ABT_lower cH sH uH vH aH (--sA) cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_PAIR_TAC "A" "H"
    ["A",(`&33 / &20`,`&33 / &20`); "A",(`&2`,`&87 / &50`);
     "H",(`&33 / &20`,`&47 / &20`); "H",(`&47 / &20`,`&47 / &20`)]);;

(* Lean: transverse_orders *)
let C868CSEP_TRANSVERSE_ORDERS = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     (ABT_upper cA sA uA vA aA (--sH) cH <= vH \/
      vA + aA <= ABT_lower cH sH uH vH aH (--sA) cA)
     ==> &61 * sH < &35 * cH \/ &61 * sA < &35 * cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABT_SB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    `&87 / &50` `&2` `--sH` `cH:real` THEN
  ABT_SB_TAC [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`]
    `&47 / &20` `&47 / &20` `--sA` `cA:real` THEN
  UNDISCH_TAC `linside cA sA uA vA aA (&87 / &50) (&2)` THEN
  UNDISCH_TAC `linside cH sH uH vH aH (&47 / &20) (&47 / &20)` THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN ABT_ARITH_TAC);;

(* Lean: positive *)
let C868CSEP_POSITIVE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cA sA /\ c977cc_normal cH sH /\ aA = aH /\ &1 < aA /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&87 / &50) (&2) /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&8 / &5) (&1) /\
     ~linside cA sA uA vA aA (&1) (&8 / &5) /\
     ldisj cA sA uA vA aA cH sH uH vH aH
     ==> (ABT_upper cA sA uA vA aA (--sH) cH <= vH \/
          vA + aA <= ABT_lower cH sH uH vH aH (--sA) cA) /\
         (&61 * sH < &35 * cH \/ &61 * sA < &35 * cA)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aH`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aH:real`;
                `cA:real`; `sA:real`] C868CS_POSITIVE_SUPPORT) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aH:real`;
                `cH:real`; `sH:real`] C868CS_POSITIVE_SUPPORT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cA sA`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cH sH`)) THEN
  MP_TAC(ASSUME `c977cc_normal cA sA`) THEN MP_TAC(ASSUME `c977cc_normal cH sH`) THEN
  REWRITE_TAC[c977cc_normal] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
  [MATCH_MP_TAC C868CSEP_ALTERNATIVES THEN
   REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC;
   DISCH_TAC THEN MATCH_MP_TAC C868CSEP_TRANSVERSE_ORDERS THEN
   MAP_EVERY EXISTS_TAC [`uA:real`; `vA:real`; `aH:real`;
                         `uH:real`; `vH:real`; `aH:real`] THEN
   ASM_REWRITE_TAC[]]);;

(* Lean: negative *)
let C868CSEP_NEGATIVE = prove
 (`forall cA sA uA vA aA cH sH uH vH aH.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cA (--sA) /\ c977cc_normal cH sH /\ aA = aH /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&2) (&2) /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&47 / &20) (&47 / &20) /\
     ldisj cA sA uA vA aA cH sH uH vH aH
     ==> ABT_upper cA sA uA vA aA (--sH) cH <= vH \/
         vA + aA <= ABT_lower cH sH uH vH aH (--sA) cA`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cA (--sA)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cH sH`)) THEN
  MP_TAC(ASSUME `c977cc_normal cA (--sA)`) THEN MP_TAC(ASSUME `c977cc_normal cH sH`) THEN
  REWRITE_TAC[c977cc_normal] THEN REPEAT STRIP_TAC THEN
  ABT_SB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    `&2` `&87 / &50` `cA:real` `sA:real` THEN
  ABT_SB_TAC [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`]
    `&2` `&2` `cH:real` `sH:real` THEN
  MATCH_MP_TAC C868CSEP_ALTERNATIVES THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ABT_ARITH_TAC);;

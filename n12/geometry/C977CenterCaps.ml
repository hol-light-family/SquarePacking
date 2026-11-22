(* ========================================================================= *)
(* Port of Compact/Bridge/C977CenterCaps.lean (N12Compact.C977CenterCaps).   *)
(* Both upper support faces of the actual southwest central owner.          *)
(* Conventions of C977CentralReach.ml (p.square (orderedOwner p 5) is the   *)
(* 5-tuple c977cre_sq 5); the OpenSquare A = cA sA uA vA aA carries its unit *)
(* normal and positive side as explicit hypotheses.                         *)
(* CentralCenterCaps.signed_caps: CCC_SIGNED_CAPS.  Tag C977CC_.             *)
(* ========================================================================= *)

needs "n12/geometry/C977CentralReach.ml";;
needs "n12/geometry/CentralCenterCaps.ml";;

(* Lean: frame_caps *)
let C977CC_FRAME_CAPS = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cA sA uA vA aA. %s /\\ cA * cA + sA * sA = &1 /\\ &0 < aA /\\
      &0 < cA /\\ abs sA <= cA /\\ aA = l /\\
      (!x y. linside cA sA uA vA aA x y <=> linside %s x y) /\\
      linside %s (&2) (&2)
      ==> uA + aA <= (&47 / &20) * cA + (&33 / &20) * sA /\\
          vA + aA <= (&47 / &20) * cA - (&33 / &20) * sA"
   C977CRE_HYP (c977cre_sq 5) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = l`)) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_POINTS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_DATA) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC CCC_SIGNED_CAPS THEN ASM_REWRITE_TAC[]);;

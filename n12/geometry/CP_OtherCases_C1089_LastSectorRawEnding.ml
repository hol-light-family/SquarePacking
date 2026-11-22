(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/LastSectorRawEnding.lean      *)
(* (namespace N12Compact.Completion.OtherCases.C1089.LastSectorRawPoints).   *)
(* Joins the raw last-sector producers (LastSectorRawPoints, Input =         *)
(* c1089lsrp_input) to the eight-point ending (LastSectorEnding, Input =     *)
(* c1089lsen_input, impossible = C1089LSEN_IMPOSSIBLE).  Not a whole-case    *)
(* exclusion.  Tag C1089LSRE_.                                               *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_LastSectorRawPoints.ml";;
needs "n12/geometry/CP_OtherCases_C1089_LastSectorEnding.ml";;

(* Lean: ending_input *)
let C1089LSRE_ENDING_INPUT = prove
 (c1089lsrp_stmt [] [] (list_mk_comb(`c1089lsen_input`, C1089LSRP_Q)),
  C1089LSRP_START_TAC THEN
  c1089lsrp_have C1089LSRP_SOUTHWEST_PAIR THEN
  c1089lsrp_have C1089LSRP_NORTHWEST_PAIR THEN
  c1089lsrp_have C1089LSRP_SINGLETON_CORNER THEN
  c1089lsrp_have C1089LSRP_SOUTHEAST_EAST THEN
  c1089lsrp_have C1089LSRP_SOUTHEAST_SOUTH THEN
  c1089lsrp_have C1089LSRP_BOTTOM_ADVANCE THEN
  c1089lsrp_have C1089LSRP_SOUTHEAST_CENTER_AND_RIGHT_ORIGIN THEN
  REPEAT (FIRST_X_ASSUM (fun th -> if is_conj (concl th) && not (is_forall (concl th))
     then MAP_EVERY ASSUME_TAC (CONJUNCTS th) else NO_TAC)) THEN
  REWRITE_TAC[c1089lsen_input] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* Lean: impossible *)
let C1089LSRE_IMPOSSIBLE = prove
 (c1089lsrp_stmt [] [] `false`,
  MESON_TAC[C1089LSRE_ENDING_INPUT; C1089LSEN_IMPOSSIBLE]);;

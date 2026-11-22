(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C997FiniteCuts.lean.              *)
(* Each ownership implication checks one literal allowed list of a C997     *)
(* domain (C997Domains).  Lean  xAllowed  is the allowed list of the HOL    *)
(* domain theorem  |- cdom c997e_family m xAllowed  (C997D_X), read off     *)
(* its conclusion; Lean  s ∈ list  is  MEM s list.                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C997Domains.ml";;

(* the allowed list of |- cdom fam m al *)
let c997fc_allowed th = rand (concl th);;

(* |- !s. MEM s al ==> P[s] , by case split over the literal list *)
let c997fc_cut th p =
  let s = `s:num->bool` in
  let tm = mk_forall(s, mk_imp(mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, s),
                                       c997fc_allowed th), p)) in
  prove(tm,
    GEN_TAC THEN REWRITE_TAC[MEM] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ]);;

(* Lean: southwest_has_two *)
let C997FC_SOUTHWEST_HAS_TWO = c997fc_cut C997D_SOUTHWEST `2 IN s`;;

(* Lean: bottom_points *)
let C997FC_BOTTOM_POINTS = c997fc_cut C997D_BOTTOM `~(2 IN s) ==> 6 IN s /\ 15 IN s`;;

(* Lean: southwest_has_four *)
let C997FC_SOUTHWEST_HAS_FOUR = c997fc_cut C997D_SOUTHWEST_CENTRAL
  `~(0 IN s) ==> ~(2 IN s) ==> ~(6 IN s) ==> 4 IN s`;;

(* Lean: top_points *)
let C997FC_TOP_POINTS = c997fc_cut C997D_TOP `~(3 IN s) ==> 7 IN s /\ 17 IN s`;;

(* Lean: southeast_has_eight *)
let C997FC_SOUTHEAST_HAS_EIGHT = c997fc_cut C997D_SOUTHEAST
  `~(4 IN s) ==> ~(6 IN s) ==> 8 IN s`;;

(* Lean: right_points *)
let C997FC_RIGHT_POINTS = c997fc_cut C997D_RIGHT
  `~(8 IN s) ==> ~(7 IN s) ==> 9 IN s /\ 19 IN s`;;

(* Lean: northeast_points *)
let C997FC_NORTHEAST_POINTS = c997fc_cut C997D_NORTHEAST
  `~(7 IN s) ==> ~(9 IN s) ==> ~(17 IN s) ==> ~(19 IN s) ==> 5 IN s /\ 16 IN s`;;

(* Lean: southeast_has_eighteen *)
let C997FC_SOUTHEAST_HAS_EIGHTEEN = c997fc_cut C997D_SOUTHEAST
  `~(15 IN s) ==> ~(16 IN s) ==> 18 IN s`;;

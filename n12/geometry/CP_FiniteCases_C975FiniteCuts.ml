(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975FiniteCuts.lean.              *)
(* Literal cuts on the C975 allowed lists: |- !s. MEM s L ==> P s.  Lean's   *)
(* C997Domains.*Allowed lists are the allowed lists of the C997D_* theorems  *)
(* (CP_FiniteCases_C997Domains.ml), taken literally (c975fc_al); the named   *)
(* C975 lists are c975d_leftSingletonAllowed, c975d_leftAllowed,             *)
(* c975d_topGAllowed.  Proved by OO_LIST_CUT_TAC (decide +kernel).           *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975Domains.ml";;

let c975fc_al th = rand (concl th);;
let c975fc_cut al body defs =
  let s = `s:num->bool` in
  prove (mk_forall(s, mk_imp(mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, s), al), body)),
         OO_LIST_CUT_TAC defs);;

(* Lean: southwest *)
let C975FC_SOUTHWEST = c975fc_cut (c975fc_al C997D_SOUTHWEST) `2 IN s /\ 12 IN s` [];;

(* Lean: leftSingleton *)
let C975FC_LEFT_SINGLETON = c975fc_cut `c975d_leftSingletonAllowed` `0 IN s /\ 10 IN s`
  [c975d_leftSingletonAllowed];;

(* Lean: bottom *)
let C975FC_BOTTOM = c975fc_cut (c975fc_al C997D_BOTTOM) `~(2 IN s) ==> 6 IN s /\ 15 IN s` [];;

(* Lean: southwestCentral *)
let C975FC_SOUTHWEST_CENTRAL = c975fc_cut (c975fc_al C997D_SOUTHWEST_CENTRAL)
  `~(0 IN s) ==> ~(2 IN s) ==> ~(10 IN s) ==> ~(12 IN s) ==> 4 IN s /\ 13 IN s` [];;

(* Lean: leftWall *)
let C975FC_LEFT_WALL = c975fc_cut `c975d_leftAllowed`
  `~(0 IN s) ==> ~(13 IN s) ==> 1 IN s /\ 11 IN s` [c975d_leftAllowed];;

(* Lean: southeast *)
let C975FC_SOUTHEAST = c975fc_cut (c975fc_al C997D_SOUTHEAST)
  `~(4 IN s) ==> ~(6 IN s) ==> ~(15 IN s) ==> 8 IN s /\ (16 IN s \/ 18 IN s)` [];;

(* Lean: rightWall *)
let C975FC_RIGHT_WALL = c975fc_cut (c975fc_al C997D_RIGHT) `~(8 IN s) ==> 9 IN s /\ 19 IN s` [];;

(* Lean: top *)
let C975FC_TOP = c975fc_cut `c975d_topGAllowed` `~(1 IN s) ==> ~(3 IN s) ==> 4 IN s`
  [c975d_topGAllowed];;

(* Lean: northeast *)
let C975FC_NORTHEAST = c975fc_cut (c975fc_al C997D_NORTHEAST)
  `~(9 IN s) ==> ~(13 IN s) ==> ~(14 IN s) ==> ~(19 IN s) ==> (5 IN s \/ 7 IN s) /\ (16 IN s \/ 17 IN s)` [];;

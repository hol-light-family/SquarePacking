(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C896Domains.lean.                 *)
(* The F2/G3 census of C896: domains (|- cdom c896d_family mask list) and    *)
(* the forced-cut lemmas over the literal lists.                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C997Domains.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: family *)
let c896d_family = new_definition
 `c896d_family = {1,2,12,16,192,768,1024,2048,4096,8192,16384,32768}`;;
let C896D_F = `c896d_family`;;

(* Lean: f_count, g_count (private) *)
let C896D_F_COUNT = card_exempt C896D_F 0;;
let C896D_G_COUNT = card_exempt C896D_F 1;;

(* Lean: bottomAllowed, leftAllowed, topAllowed, northwestAllowed, rightAllowed *)
let c896d_bottom_allowed = new_definition `c896d_bottom_allowed = [{2,12}; {2,10,12}; {2,12,15}; {6,15}; {6,12,15}; {6,15,18}]`;;
let c896d_left_allowed = new_definition `c896d_left_allowed = [{0,10}; {0,10,13}; {1,11}; {1,11,13}]`;;
let c896d_top_allowed = new_definition `c896d_top_allowed = [{3,14}; {3,11,14}; {3,14,17}; {7,17}; {7,14,17}; {7,17,19}]`;;
let c896d_northwest_allowed = new_definition `c896d_northwest_allowed = [{1,11}; {1,13}; {1,14}; {1,11,13}; {1,11,14}; {1,13,14}; {3,11}; {3,13}; {3,14}; {3,11,13}; {3,11,14}; {3,13,14}; {5,11}; {5,13}; {5,14}; {5,11,13}; {5,11,14}; {5,13,14}; {5,13,16}; {5,13,17}; {5,14,16}; {5,14,17}]`;;
let c896d_right_allowed = new_definition `c896d_right_allowed = [{8,18}; {8,16,18}; {9,19}; {9,16,19}]`;;

(* Lean: bottom, left, top, northwest, right (restrict = restrictFCardOne) *)
let C896D_BOTTOM = cdom_named (ro_restrict_f1 (ro_combined C896D_F 19)) c896d_bottom_allowed;;
let C896D_LEFT = cdom_named (ro_restrict_f1 (ro_combined C896D_F 17)) c896d_left_allowed;;
let C896D_TOP = cdom_named (ro_restrict_f1 (ro_combined C896D_F 24)) c896d_top_allowed;;
let C896D_NORTHWEST = cdom_named (ro_restrict_f1 (ro_combined C896D_F 13)) c896d_northwest_allowed;;
let C896D_RIGHT = cdom_named (ro_restrict_f1 (ro_combined C896D_F 21)) c896d_right_allowed;;

(* Lean: northeastF *)
let C896D_NORTHEAST_F = ro_single C896D_F 34;;

(* Lean: bottom_forced (and the private bottom_cut) *)
let C896D_BOTTOM_FORCED = prove
 (`forall s. MEM s c896d_bottom_allowed /\ ~(2 IN s) ==> 6 IN s /\ 15 IN s`,
  OO_LIST_CUT_TAC [c896d_bottom_allowed]);;
(* Lean: left_forced *)
let C896D_LEFT_FORCED = prove
 (`forall s. MEM s c896d_left_allowed /\ ~(0 IN s) ==> 1 IN s /\ 11 IN s`,
  OO_LIST_CUT_TAC [c896d_left_allowed]);;
(* Lean: top_forced *)
let C896D_TOP_FORCED = prove
 (`forall s. MEM s c896d_top_allowed /\ ~(7 IN s) ==> 3 IN s /\ 14 IN s`,
  OO_LIST_CUT_TAC [c896d_top_allowed]);;
(* Lean: northwest_forced *)
let C896D_NORTHWEST_FORCED = prove
 (`forall s. MEM s c896d_northwest_allowed /\ ~(1 IN s) /\ ~(3 IN s) /\ ~(11 IN s) /\ ~(14 IN s)
       ==> 5 IN s /\ 13 IN s`,
  OO_LIST_CUT_TAC [c896d_northwest_allowed]);;
(* Lean: right_forced *)
let C896D_RIGHT_FORCED = prove
 (`forall s. MEM s c896d_right_allowed /\ ~(9 IN s) ==> 8 IN s /\ 18 IN s`,
  OO_LIST_CUT_TAC [c896d_right_allowed]);;

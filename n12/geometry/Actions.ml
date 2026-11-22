(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C1092WallSymmetry/Actions.lean.                   *)
(* Owner, wall, central and Boolean actions for the original C1092 family.  *)
(* A Lean Transform <swap, reflectX, reflectY> is a triple                  *)
(* (sw, rx, ry) : bool#bool#bool;  Fin n -> Fin m tables are HOL lists      *)
(* (f i = EL i list);  a WallBranch is br : num->bool (C1092WallCycle.ml);   *)
(* symmetry is the list c1092ws_symmetry of the 8 triples; canonicalBranch i *)
(* is c1092ws_canonical_branch i : num->bool.                                *)
(* ========================================================================= *)

needs "n12/geometry/C1092WallCycle.ml";;

(* Lean: ownerX, ownerY, ownerSwap *)
let c1092ws_ownerX = new_definition `c1092ws_ownerX = [1;0;3;2;5;4;7;6;10;9;8;11]`;;
let c1092ws_ownerY = new_definition `c1092ws_ownerY = [3;2;1;0;7;6;5;4;8;11;10;9]`;;
let c1092ws_ownerSwap = new_definition `c1092ws_ownerSwap = [0;3;2;1;4;7;6;5;9;8;11;10]`;;

(* Lean: ownerAction *)
let c1092ws_owner_action = new_definition
 `c1092ws_owner_action (g:bool#bool#bool) (i:num) =
    let j = if FST g then EL i c1092ws_ownerSwap else i in
    let k = if SND (SND g) then EL j c1092ws_ownerY else j in
    if FST (SND g) then EL k c1092ws_ownerX else k`;;

(* Lean: wallX, wallY, wallSwap, wallAction *)
let c1092ws_wallX = new_definition `c1092ws_wallX = [2;1;0;3]`;;
let c1092ws_wallY = new_definition `c1092ws_wallY = [0;3;2;1]`;;
let c1092ws_wallSwap = new_definition `c1092ws_wallSwap = [1;0;3;2]`;;
let c1092ws_wall_action = new_definition
 `c1092ws_wall_action (g:bool#bool#bool) (i:num) =
    let j = if FST g then EL i c1092ws_wallSwap else i in
    let k = if SND (SND g) then EL j c1092ws_wallY else j in
    if FST (SND g) then EL k c1092ws_wallX else k`;;

(* Lean: centralX, centralY, centralSwap, centralAction *)
let c1092ws_centralX = new_definition `c1092ws_centralX = [1;0;3;2]`;;
let c1092ws_centralY = new_definition `c1092ws_centralY = [3;2;1;0]`;;
let c1092ws_centralSwap = new_definition `c1092ws_centralSwap = [0;3;2;1]`;;
let c1092ws_central_action = new_definition
 `c1092ws_central_action (g:bool#bool#bool) (i:num) =
    let j = if FST g then EL i c1092ws_centralSwap else i in
    let k = if SND (SND g) then EL j c1092ws_centralY else j in
    if FST (SND g) then EL k c1092ws_centralX else k`;;

let C1092WS_LOOKUPS =
  List.concat (map (fun th -> Array.to_list (el_lookups th))
    [c1092ws_ownerX; c1092ws_ownerY; c1092ws_ownerSwap; c1092ws_wallX; c1092ws_wallY; c1092ws_wallSwap;
     c1092ws_centralX; c1092ws_centralY; c1092ws_centralSwap]) @ C1092WC_LISTS;;

let C1092WS_ACTION_TAC =
  REWRITE_TAC[FORALL_PAIR_THM] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  C1092WP_ENUM_TAC `k:num` 4 THEN
  MAP_EVERY BOOL_CASES_TAC [`p1:bool`; `p1':bool`; `p2:bool`] THEN
  REWRITE_TAC[c1092ws_owner_action; c1092ws_wall_action; c1092ws_central_action; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC C1092WS_LOOKUPS THEN REPEAT(CHANGED_TAC(REWRITE_TAC C1092WS_LOOKUPS));;

(* Lean: ownerAction_wall *)
let C1092WS_OWNERACTION_WALL = prove
 (`forall g k. k < 4 ==> c1092ws_owner_action g (EL k c1092wc_wall) =
                   EL (c1092ws_wall_action g k) c1092wc_wall`,
  C1092WS_ACTION_TAC);;

(* Lean: ownerAction_central *)
let C1092WS_OWNERACTION_CENTRAL = prove
 (`forall g k. k < 4 ==> c1092ws_owner_action g (EL k c1092wc_central) =
                   EL (c1092ws_central_action g k) c1092wc_central`,
  C1092WS_ACTION_TAC);;

(* Lean: ownerAction_corner *)
let C1092WS_OWNERACTION_CORNER = prove
 (`forall g k. k < 4 ==> c1092ws_owner_action g (EL k c1092wc_corner) =
                   EL (c1092ws_central_action g k) c1092wc_corner`,
  C1092WS_ACTION_TAC);;

(* Lean: wallFlip *)
let c1092ws_wall_flip = new_definition
 `c1092ws_wall_flip (g:bool#bool#bool) (k:num) =
    if FST g then EL k [FST (SND g); SND (SND g); FST (SND g); SND (SND g)]
    else EL k [SND (SND g); FST (SND g); SND (SND g); FST (SND g)]`;;

(* Lean: branchAction *)
let c1092ws_branch_action = new_definition
 `c1092ws_branch_action (g:bool#bool#bool) (br:num->bool) (k:num) =
    if c1092ws_wall_flip g k then ~(br (c1092ws_wall_action g k)) else br (c1092ws_wall_action g k)`;;

(* Lean: symmetry *)
let c1092ws_symmetry = new_definition
 `c1092ws_symmetry : (bool#bool#bool)list =
    [(false,false,false); (false,false,true); (false,true,false); (false,true,true); (true,false,false); (true,false,true); (true,true,false); (true,true,true)]`;;

(* Lean: canonicalBranch *)
let c1092ws_canonical_branch = new_definition
 `c1092ws_canonical_branch (i:num) (k:num) =
    EL k (EL i [[true;false;false;true]; [true;true;true;false]; [true;false;true;false]; [true;true;false;false]])`;;

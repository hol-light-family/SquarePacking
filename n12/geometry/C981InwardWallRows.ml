(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981InwardWallRows.lean                           *)
(* (namespace N12Compact.C981InwardWallRows).  Original vectors 36 and 106   *)
(* share one wall-owner obstruction (C981InwardWall.impossible =             *)
(* C981IW_IMPOSSIBLE at owner 8); the foreign singleton point is strictly    *)
(* owned by original owner 1.                                                *)
(* Lean `Check v` quantifies over the computed lists queryInsidePoints /     *)
(* queryOutsidePoints; `excludes v checked` is the producer                  *)
(* c981iwr_excludes V (literal V): it builds each membership with            *)
(* c981br_in / c981br_out (Bridge_C981Row27.ml), which fail exactly when the *)
(* point is not in the list, and returns |- c981vd_excludes_vector V.        *)
(* ========================================================================= *)

needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/C981InwardWall.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;

(* Lean: Check, excludes *)
let c981iwr_excludes v =
  c981br_prove_excl v C981IW_IMPOSSIBLE [8]
   [c981br_in v 8 (`&457 / &500`, `&2`);
    c981br_in v 8 (`&1`, `&12 / &5`);
    c981br_in v 8 (`&87 / &50`, `&2`);
    c981br_out v 8 (`&1`, `&87 / &50`);
    c981br_out v 8 (`&33 / &20`, `&47 / &20`);
    c981br_excl v 8 1 (`&19 / &25`, `&187 / &100`)];;

(* Lean: coveredIds *)
let c981iwr_covered_ids = new_definition
 `c981iwr_covered_ids = [36; 106]`;;

(* Lean: checked *)
let C981IWR_CHECKED = map (fun i -> c981br_rep_excluded i c981iwr_excludes) [36; 106];;

(* Lean: covered_excluded *)
let C981IWR_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981iwr_covered_ids] (c981br_covered [36; 106] C981IWR_CHECKED);;

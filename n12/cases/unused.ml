(* The 2 FourSquareUnused cases 841, 842 (Jatloe: Compact/Cases/FourSquareUnused, via
   Bridge/FourSquareConvexCase): template FourSquareLowerBarrier, as the Variant cases.
   The convex (triangle) point witness of case 842 is re-found by gen_bridge's point search. *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/gen_bridge.ml";;
needs "n12/geometry/cornerpair.ml";;
needs "n12/geometry/unused_data.ml";;
needs "n12/geometry/FourSquareLowerBarrier.ml";;
let unused_case_thm (cid, fam, doms, trf, masks, owned, lb, rb) =
  let (mk, me) = chop_list 4 masks and (ok, oe) = chop_list 4 owned in
  gen_case_thm_x (zip me oe) FSLB_IMPOSSIBLE (cid, fam, doms, trf, mk, ok);;
let UNUSED_CASE_THMS = map check_case_thm
  (run_cases "UNUSED" unused_case_thm (fun (cid,_,_,_,_,_,_,_) -> cid) VAR_Unused);;

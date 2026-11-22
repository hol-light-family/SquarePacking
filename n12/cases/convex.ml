(* ========================================================================= *)
(* The 9 FourSquareConvex cases (Jatloe: Compact/Cases/FourSquareConvex,     *)
(* Bridge/FourSquareConvexCase): template FourSquareLowerBarrier with a      *)
(* fifth forced owner; domains include promoted budgets (992, 1001) and the  *)
(* upper-middle domain 33792 (862, 864).  Hull witnesses are found by        *)
(* derive_point.  Result: CONVEX_CASE_THMS : (int * thm) list.               *)
(* ========================================================================= *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/bridge_ext.ml";;
needs "n12/geometry/FourSquareLowerBarrier.ml";;
loadt "n12/geometry/fsc_data.ml";;

let convex_case_thm (cid, fam, doms, trf, masks, owned, lb, rb, promo) =
  let (mk, me) = chop_list 4 masks and (ok, oe) = chop_list 4 owned in
  let xm = match promo with Some (pm, _) -> [pm] | None -> [] in
  gen_case_thm_y (xdfun promo) xm (zip me oe) FSLB_IMPOSSIBLE (cid, fam, doms, trf, mk, ok);;

let CONVEX_CASE_THMS = map check_case_thm
  (run_cases "CONVEX" convex_case_thm (fun (cid,_,_,_,_,_,_,_,_) -> cid) FSC_CASES);;

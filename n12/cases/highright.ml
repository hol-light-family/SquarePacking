(* The 13 FourSquareHighRight and 8 FourSquareHighRightExtra cases (Jatloe: Compact/Cases/
   FourSquareHighRight{,Extra}, Bridge/FourSquareCaseHighRight): template FourSquareHighRight. *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/gen_bridge.ml";;
needs "n12/geometry/cornerpair.ml";;
needs "n12/geometry/hr_data.ml";;
needs "n12/geometry/FourSquareHighRight.ml";;
let hr_case_thm (cid, fam, doms, trf, masks, owned, lb, rb) =
  let (mk, me) = chop_list 4 masks and (ok, oe) = chop_list 4 owned in
  gen_case_thm_x (zip me oe) FSHR_IMPOSSIBLE (cid, fam, doms, trf, mk, ok);;
let HR_CASE_THMS = map check_case_thm
  (run_cases "HIGHRIGHT" hr_case_thm (fun (cid,_,_,_,_,_,_,_) -> cid)
     (VAR_FourSquareHighRight @ VAR_FourSquareHighRightExtra));;

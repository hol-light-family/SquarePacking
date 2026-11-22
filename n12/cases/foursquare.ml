(* The 15 FourSquare cases (Jatloe: Compact/Cases/FourSquare, Bridge/FourSquareCase). *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/fs_bridge.ml";;
needs "n12/geometry/fs_data.ml";;
needs "n12/geometry/FourSquareTemplate.ml";;
let FS_CASE_THMS = map check_case_thm
  (run_cases "FOURSQUARE" (fun c -> let (ri, th) = fs_case_thm c in (ri, MP th FST_IMPOSSIBLE))
     (fun (cid,_,_,_,_,_,_,_) -> cid) FS_CASES);;

(* All case drivers of the cs2 session (load after n12/cases/cs_load.ml).
   FourSquareConvex, OppositeCentralWalls, MergedTopFurther, C849851,
   MergedLower, Endpoint684, C84. *)
loadt "n12/cases/convex.ml";;
loadt "n12/cases/ocw.ml";;
loadt "n12/cases/handcases.ml";;
loadt "n12/cases/mergedlower.ml";;
loadt "n12/cases/c84.ml";;
loadt "n12/cases/hrx.ml";;
loadt "n12/cases/unused.ml";;
let CS2_CASE_THMS = CONVEX_CASE_THMS @ OCW_CASE_THMS @ MTF_CASE_THMS @ C849851_CASE_THMS @
  MERGEDLOWER_CASE_THMS @ ENDPOINT684_CASE_THMS @ C84_CASE_THMS @ HRX_CASE_THMS @ UNUSED_CASE_THMS;;
Printf.printf "CS2: %d case theorems\n%!" (length CS2_CASE_THMS);;

(* ========================================================================= *)
(* MergedLower (71, 80, 589, 590; Jatloe Compact/Cases/MergedLower,          *)
(* Bridge/FourSquareVectorCover) and Endpoint684 (Compact/Cases/Endpoint684). *)
(* Every consistent assignment of the nine relaxed/transformed domains is    *)
(* closed by one recipe: FourSquareCase (FST template), MidpointCase (MPRT    *)
(* template, topX = 8/5), FourSquareCaseHighRight (FSHR) or                  *)
(* EndpointHighRightCase (EHR).                                              *)
(* Result: MERGEDLOWER_CASE_THMS, ENDPOINT684_CASE_THMS.                      *)
(* ========================================================================= *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/bridge_ext.ml";;
needs "n12/geometry/FourSquareTemplate.ml";;
needs "n12/geometry/MidpointRowTemplate.ml";;
needs "n12/geometry/FourSquareHighRight.ml";;
needs "n12/geometry/EndpointHighRight.ml";;
loadt "n12/geometry/ml_data.ml";;

(* MidpointRowTemplate.impossible at topX = 8/5 (the only value used by MergedLower) *)
let MPRT_IMPOSSIBLE_85 =
  let vs = fst (strip_forall (concl MPRT_IMPOSSIBLE)) in
  let (v20, _) = chop_list 20 vs in
  GENL v20 (SPECL (v20 @ [`&8 / &5`]) MPRT_IMPOSSIBLE);;

let ML_ID = (false, false, false) and ML_RX = (false, true, false);;
let upperNE a b l r = (FST_IMPOSSIBLE, ML_ID, [1024; 2048; 4096; 16384], [a; b; l; r]);;
let upperNW a b l r = (FST_IMPOSSIBLE, ML_RX, [2048; 1024; 16384; 4096], [b; a; r; l]);;
let spanNE a b l r = (MPRT_IMPOSSIBLE_85, ML_ID, [1024; 2048; 4096; 16384], [a; b; l; r]);;
let spanNW a b l r = (MPRT_IMPOSSIBLE_85, ML_RX, [2048; 1024; 16384; 4096], [b; a; r; l]);;

let ML_RECIPES =
  [upperNE [5;13;16] [3;14] [1;11] [9;19];
   upperNE [5;16] [3;13;14] [1;11] [9;19];
   upperNE [5;16] [3;14] [1;11] [9;19];
   upperNE [5;16] [3;14] [1;11;13] [9;19];
   upperNW [7;16;17] [5;13] [1;11] [9;19];
   upperNW [7;17] [5;13] [1;11] [9;16;19];
   upperNW [7;17] [5;13] [1;11] [9;19];
   upperNW [7;17] [5;13;16] [1;11] [9;19];
   spanNE [5;14;16] [3;13] [1;11] [9;19];
   spanNE [5;16] [3;13] [1;11] [9;19];
   spanNW [7;16] [5;13] [1;11] [9;19];
   spanNW [7;16] [5;13;17] [1;11] [9;19]];;

(* Endpoint684: roles 256,512,16384,2 under the half-turn; FSHR or EHR per pattern *)
let E684_ROLES = [256; 512; 16384; 2] and E684_TRF = (false, true, true);;
let E684_RECIPES = List.concat (map (fun ow ->
    [(FSHR_IMPOSSIBLE, E684_TRF, E684_ROLES, ow); (EHR_IMPOSSIBLE, E684_TRF, E684_ROLES, ow)])
  [[[4;13];[6;15];[8;18];[0;10]];
   [[4;13];[6;16];[8;18];[0;10]];
   [[4;13];[6;15;16];[8;18];[0;10]];
   [[4;13;15];[6;16];[8;18];[0;10]];
   [[4;13;16];[6;15];[8;18];[0;10]];
   [[4;13];[6;15];[8;16;18];[0;10]]]);;

let ml_case_thm recipes (cid, fam, doms) = gen_enum_thm (xdfun None) [] recipes (cid, fam, doms);;

let MERGEDLOWER_CASE_THMS = map check_case_thm
  (run_cases "MERGEDLOWER" (ml_case_thm ML_RECIPES) (fun (cid,_,_) -> cid)
     (filter (fun (cid,_,_) -> cid <> 684) ML_CASES));;
let ENDPOINT684_CASE_THMS = map check_case_thm
  (run_cases "ENDPOINT684" (ml_case_thm E684_RECIPES) (fun (cid,_,_) -> cid)
     (filter (fun (cid,_,_) -> cid = 684) ML_CASES));;

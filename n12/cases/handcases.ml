(* ========================================================================= *)
(* MergedTopFurther (697-699; Jatloe Cases/MergedTopFurther) and C849851     *)
(* (849, 851; Cases/C849851): forced owners (certified_domain_forced) and the *)
(* whole-case geometry of hand_wrappers.ml, applied by the case engine.      *)
(* Result: MTF_CASE_THMS, C849851_CASE_THMS.                                 *)
(* ========================================================================= *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/bridge_ext.ml";;
needs "n12/geometry/hand_wrappers.ml";;
needs "n12/geometry/c84_bridge.ml";;

(* MergedTopFurther.domain34816: singleton x singleton without the sets containing
   15 or 18 (merged_top_diameter, from the seed (2,1543/500)) *)
let hand_dfun sq_of hnp hrow r sq d =
  let (m, _, _, _, _) = sq in
  let th = xdfun None sq_of hnp hrow r sq d in
  if m = 34816 then diam_remove hnp sq th [15; 18] (`&2`, `&1543 / &500`) else th;;

(* forced owners + one template over the original squares *)
let hand_case_thm dfun tmpl roles masks owned (cid, fam, doms) =
  let ctx = case_ctx dfun [] (cid, fam, doms) in
  let eqs = map2 (fun m v -> (m, forced_eq ctx m v)) masks owned in
  close_case ctx (apply_tmpl ctx eqs tmpl (false, false, false) roles);;

(* MergedTopFurther/Ownership.lean *)
let mtf_variant (cid, bottom, right) =
  let fam = [1; 2; 12; 16; 32; 192; 256; 1024; 4096; bottom; right; 34816] in
  let db = if bottom = 8704 then Xd(Dprod(Hspec(74,0), Hsing 1)) else Xd(Dcomb 18) in
  let dr = if right = 16896 then Xd(Dprod(Hspec(85,0), Hsing 1)) else Xd(Dcomb 20) in
  (cid, fam, [(1, Xd(Dcomb 0)); (2, Xd(Dcomb 2)); (16, Xd(Dprod(Hspec(14,0), Hspec(16,1))));
              (32, Xd(Dprod(Hspec(17,0), Hspec(18,1)))); (256, Xd(Dcomb 5));
              (1024, Xd(Dprod(Hspec(34,0), Hspec(35,1)))); (4096, Xd(Dcomb 16));
              (bottom, db); (right, dr); (34816, Xd(Dprod(Hsing 0, Hsing 1)))],
   [1; 2; 16; 32; 256; 1024; 4096; bottom; right; 34816]);;
let MTF_OWNED = [[2;12]; [0;10]; [7;17]; [9;19]; [4;13]; [5;16]; [1;11]; [6;15]; [8;18]; [3;14]];;
let MTF_CASES = map mtf_variant [(697, 8192, 16384); (698, 8192, 16896); (699, 8704, 16384)];;
(* roles: A = 1024, B = 34816, R = 32, C = 16, E = 192, L = 4096 *)
let MTF_CASE_THMS = map check_case_thm
  (run_cases "MERGEDTOPFURTHER"
     (fun (cid, fam, doms, masks) ->
        hand_case_thm hand_dfun MTF_IMPOSSIBLE [1024; 34816; 32; 16; 192; 4096] masks MTF_OWNED (cid, fam, doms))
     (fun (cid,_,_,_) -> cid) MTF_CASES);;

(* C849851/Ownership.lean *)
let c849_variant (cid, right) =
  let fam = [1; 2; 12; 16; 192; 256; 512; 1024; 4096; 8192; right; 34816] in
  let dr = if right = 16416 then Xd(Dprod(Hspec(82,0), Hspec(83,1))) else Xd(Dcomb 20) in
  (cid, fam, [(1, Xd(Dcomb 0)); (2, Xd(Dcomb 2)); (16, Xd(Dprod(Hspec(14,0), Hspec(16,1))));
              (4096, Xd(Dcomb 16)); (8192, Xd(Dcomb 18)); (256, Xd(Dcomb 5)); (512, Xd(Dcomb 7));
              (1024, Xd(Dprod(Hspec(34,0), Hspec(35,1)))); (right, dr);
              (34816, Xd(Dprod(Hsing 0, Hsing 1)))],
   [1; 2; 16; 4096; 8192; 256; 512; 1024; right; 34816], right);;
let C849_OWNED = [[2;12]; [0;10]; [7;17]; [1;11]; [6;15]; [4;13]; [8;18]; [5;16]; [9;19]; [3;14]];;
let C849_CASES = map c849_variant [(849, 16384); (851, 16416)];;
(* roles: A = 1024, R = right, B = 34816, C = 16, E = 192, L = 4096 *)
let C849851_CASE_THMS = map check_case_thm
  (run_cases "C849851"
     (fun (cid, fam, doms, masks, right) ->
        hand_case_thm (xdfun None) C849851_IMPOSSIBLE [1024; right; 34816; 16; 192; 4096] masks C849_OWNED (cid, fam, doms))
     (fun (cid,_,_,_,_) -> cid) C849_CASES);;

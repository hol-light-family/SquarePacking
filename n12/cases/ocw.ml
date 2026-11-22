(* ========================================================================= *)
(* OppositeCentralWalls (709, 882, 890, 1075, 1077, 1078, 1081, 1083;        *)
(* Jatloe Compact/Cases/OppositeCentralWalls/{Ownership,Complete}).          *)
(* Six forced owners; CentralWallCenter.point under reflectY (roles 512,     *)
(* 16384, 8192) and reflectX (roles 2048, 4096, 32768) puts owners 512 and   *)
(* 2048 both at (2,2), contradicting disjointness.                           *)
(* Result: OCW_CASE_THMS.                                                    *)
(* ========================================================================= *)
needs "n12/cases/case_util.ml";;
needs "n12/geometry/bridge_ext.ml";;
needs "n12/geometry/CentralWallCenter.ml";;

let OCW_MASKS = [512; 2048; 4096; 8192; 16384; 32768]
and OCW_OWNED = [[4;16]; [5;13]; [1;11]; [6;15]; [8;18]; [3;14]];;

(* Ownership.lean: family v and domains v *)
let ocw_variant (cid, low, corner, middle) =
  let fam = [1; low; 12; corner; 192; 512; middle; 2048; 4096; 8192; 16384; 32768] in
  let dlow = match low with
      2 -> Xd(Dcomb 2) | 256 -> Xd(Dcomb 5)
    | 258 -> Xd(Dprod(Hspec(24,0), Hsing 1)) | _ -> failwith "low" in
  let dcorner = match corner with
      16 -> Xd(Dprod(Hspec(14,0), Hspec(16,1))) | 32 -> Xd(Dprod(Hspec(17,0), Hspec(18,1)))
    | _ -> failwith "corner" in
  let dmiddle = match middle with
      32 -> Xd(Dprod(Hspec(17,0), Hspec(18,1)))
    | 1024 -> Xd(Dprod(Hspec(34,0), Hspec(35,1)))
    | 1056 -> Xd(Dprod(Hspec(38,0), Hsing 1))
    | 1040 -> Xd(Dcomb 10) | _ -> failwith "middle" in
  (cid, fam, [(1, Xd(Dcomb 0)); (low, dlow); (corner, dcorner); (512, Xd(Dcomb 7)); (middle, dmiddle);
              (2048, Xd(Dcomb 12)); (4096, Xd(Dcomb 16)); (8192, Xd(Dcomb 18));
              (16384, Xd(Dcomb 20)); (32768, Xd(Dcomb 22))]);;

let OCW_CASES = map ocw_variant
  [(709, 2, 16, 32); (882, 2, 16, 1024); (890, 2, 16, 1056); (1075, 256, 16, 1056);
   (1077, 258, 16, 1056); (1078, 256, 32, 1024); (1081, 256, 32, 1040); (1083, 258, 32, 1040)];;

let base_params_of ctx m =
  let (_, iv, _, _, _) = csq ctx m in
  let [c1t; c2t; at; bt; lt] = sq_params iv in lsq_params c1t c2t at bt lt;;

let ocw_case_thm (cid, fam, doms) =
  let ctx = case_ctx (xdfun None) [] (cid, fam, doms) in
  let eqs = map2 (fun m v -> (m, forced_eq ctx m v)) OCW_MASKS OCW_OWNED in
  let centre trf roles =
    let th = apply_tmpl ctx eqs CWC_POINT trf roles in
    let peq = pull_point_eq trf (base_params_of ctx (hd roles)) (`&2`, `&2`) in
    let th' = EQ_MP peq th in
    if rand(concl th') = `&2` && rand(rator(concl th')) = `&2` then th' else failwith "ocw: centre" in
  let se = centre (false, false, true) [512; 16384; 8192]
  and nw = centre (false, true, false) [2048; 4096; 32768] in
  let sa = csq ctx 512 and sb = csq ctx 2048 in
  let (_, _, lta, _, _) = sa and (_, _, ltb, _, _) = sb in
  let dis = MATCH_MP NPACK_LDISJ (end_itlist CONJ [ctx.hnp; lta; ltb; cneq_sq sa sb]) in
  let f = MP (NOT_ELIM (SPECL [`&2`; `&2`] (REWRITE_RULE[ldisj] dis))) (CONJ se nw) in
  close_case ctx f;;

let OCW_CASE_THMS = map check_case_thm
  (run_cases "OCW" ocw_case_thm (fun (cid,_,_) -> cid) OCW_CASES);;

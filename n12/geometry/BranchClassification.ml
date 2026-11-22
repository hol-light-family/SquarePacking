(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C1092WallSymmetry/BranchClassification.lean.      *)
(* The sixteen wall-sign patterns under the eight container symmetries.     *)
(* S12.allTransforms is the HOL list c1092wsb_all_transforms of triples      *)
(* (swap, reflectX, reflectY);  a WallBranch Fin 4 -> Bool is br : num->bool *)
(* and equality of WallBranches is equality on k < 4.                        *)
(* ========================================================================= *)

needs "n12/geometry/Actions.ml";;

(* Lean: S12.allTransforms *)
let c1092wsb_all_transforms = new_definition
 `c1092wsb_all_transforms : (bool#bool#bool)list =
    [(false,false,false); (false,false,true); (false,true,false); (false,true,true); (true,false,false); (true,false,true); (true,true,false); (true,true,true)]`;;

let C1092WSB_SYM_ELS = el_lookups c1092ws_symmetry;;
let C1092WSB_CANON = prove
 (`(forall k. c1092ws_canonical_branch 0 k = EL k [true;false;false;true]) /\
   (forall k. c1092ws_canonical_branch 1 k = EL k [true;true;true;false]) /\
   (forall k. c1092ws_canonical_branch 2 k = EL k [true;false;true;false]) /\
   (forall k. c1092ws_canonical_branch 3 k = EL k [true;true;false;false])`,
  REWRITE_TAC[c1092ws_canonical_branch] THEN CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]);;

(* Lean: symmetry_mem *)
let C1092WSB_SYMMETRY_MEM = prove
 (`forall u. u < 8 ==> MEM (EL u c1092ws_symmetry) c1092wsb_all_transforms`,
  GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `u:num` 8 THEN
  REWRITE_TAC(Array.to_list C1092WSB_SYM_ELS) THEN REWRITE_TAC[c1092wsb_all_transforms; MEM; PAIR_EQ]);;

(* evaluate branch_action (EL u symmetry) br k for literal u, k *)
let C1092WSB_EVAL_TAC =
  REWRITE_TAC(Array.to_list C1092WSB_SYM_ELS) THEN
  REWRITE_TAC[c1092ws_branch_action; c1092ws_wall_flip; c1092ws_wall_action; LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC[] THEN REWRITE_TAC C1092WS_LOOKUPS THEN
  CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[];;

(* the action of symmetry u on the pattern (b0,b1,b2,b3), computed in OCaml *)
let c1092wsb_wall_action (sw, rx, ry) i =
  let j = if sw then List.nth [1;0;3;2] i else i in
  let k = if ry then List.nth [0;3;2;1] j else j in
  if rx then List.nth [2;1;0;3] k else k;;
let c1092wsb_flip (sw, rx, ry) k =
  if sw then List.nth [rx; ry; rx; ry] k else List.nth [ry; rx; ry; rx] k;;
let c1092wsb_syms = [(false,false,false); (false,false,true); (false,true,false); (false,true,true);
                     (true,false,false); (true,false,true); (true,true,false); (true,true,true)];;
let c1092wsb_act g b =
  map (fun k -> let x = List.nth b (c1092wsb_wall_action g k) in if c1092wsb_flip g k then not x else x) (0--3);;
let c1092wsb_canon = [[true;false;false;true]; [true;true;true;false]; [true;false;true;false]; [true;true;false;false]];;

(* Lean: branch_coverage *)
let C1092WSB_BRANCH_COVERAGE = prove
 (`forall br:num->bool. exists u k. u < 8 /\ k < 4 /\
     forall j. j < 4 ==> c1092ws_branch_action (EL u c1092ws_symmetry) br j = c1092ws_canonical_branch k j`,
  GEN_TAC THEN
  ASM_CASES_TAC `(br:num->bool) 0` THEN ASM_CASES_TAC `(br:num->bool) 1` THEN
  ASM_CASES_TAC `(br:num->bool) 2` THEN ASM_CASES_TAC `(br:num->bool) 3` THEN
  (fun (asl, w as g) ->
     let bval i = let t = mk_comb(`br:num->bool`, mk_small_numeral i) in
                  exists (fun (_, th) -> concl th = t) asl in
     let b = map bval (0--3) in
     let (u, k) = find (fun (u, k) -> c1092wsb_act (List.nth c1092wsb_syms u) b = List.nth c1092wsb_canon k)
                    (List.concat (map (fun u -> map (fun k -> (u, k)) (0--3)) (0--7))) in
     (EXISTS_TAC (mk_small_numeral u) THEN EXISTS_TAC (mk_small_numeral k) THEN
      CONV_TAC NUM_REDUCE_CONV THEN GEN_TAC THEN DISCH_TAC THEN C1092WP_ENUM_TAC `j:num` 4 THEN
      REWRITE_TAC[C1092WSB_CANON] THEN C1092WSB_EVAL_TAC THEN ASM_REWRITE_TAC[]) g));;

(* the 32 action tables  |- branch_action (EL u symmetry) (canonical_branch i) k = b, k < 4 *)
let C1092WSB_TABLE = Array.init 8 (fun u -> Array.init 4 (fun i -> Array.init 4 (fun k ->
  let v = List.nth (c1092wsb_act (List.nth c1092wsb_syms u) (List.nth c1092wsb_canon i)) k in
  let tm = mk_eq(list_mk_comb(`c1092ws_branch_action`,
              [mk_comb(mk_comb(`EL:num->(bool#bool#bool)list->bool#bool#bool`, mk_small_numeral u), `c1092ws_symmetry`);
               mk_comb(`c1092ws_canonical_branch`, mk_small_numeral i); mk_small_numeral k]),
             if v then `true` else `false`) in
  prove(tm, C1092WSB_EVAL_TAC THEN REWRITE_TAC[C1092WSB_CANON] THEN
            CONV_TAC(ONCE_DEPTH_CONV EL_CONV) THEN REWRITE_TAC[]))));;

(* Lean: canonical_orbits_disjoint *)
let C1092WSB_CANONICAL_ORBITS_DISJOINT = prove
 (`forall u v i j. u < 8 /\ v < 8 /\ i < 4 /\ j < 4 /\
     (forall k. k < 4 ==> c1092ws_branch_action (EL u c1092ws_symmetry) (c1092ws_canonical_branch i) k =
                    c1092ws_branch_action (EL v c1092ws_symmetry) (c1092ws_canonical_branch j) k)
     ==> i = j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  C1092WP_ENUM_TAC `u:num` 8 THEN C1092WP_ENUM_TAC `v:num` 8 THEN
  C1092WP_ENUM_TAC `i:num` 4 THEN C1092WP_ENUM_TAC `j:num` 4 THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  (fun (asl, w as g) ->
     let h = snd (find (fun (_, th) -> is_forall (concl th)) asl) in
     let args t = let _, xs = strip_comb t in xs in
     let l = lhand (rand (snd (dest_forall (concl h)))) and r = rand (rand (snd (dest_forall (concl h)))) in
     let num_of t = dest_small_numeral t in
     let u = num_of (lhand (hd (args l))) and i = num_of (rand (List.nth (args l) 1)) in
     let v = num_of (lhand (hd (args r))) and j = num_of (rand (List.nth (args r) 1)) in
     let k = find (fun k -> C1092WSB_TABLE.(u).(i).(k) |> concl |> rhs <>
                            (C1092WSB_TABLE.(v).(j).(k) |> concl |> rhs)) (0--3) in
     (MP_TAC(SPEC (mk_small_numeral k) h) THEN CONV_TAC NUM_REDUCE_CONV THEN
      REWRITE_TAC[C1092WSB_TABLE.(u).(i).(k); C1092WSB_TABLE.(v).(j).(k)]) g));;

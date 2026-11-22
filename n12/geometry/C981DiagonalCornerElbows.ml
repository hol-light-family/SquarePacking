(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981DiagonalCornerElbows.lean                     *)
(* (namespace N12Compact.C981DiagonalCornerElbows).  The diagonal wall and   *)
(* its genuine foreign paired corner close the elbow angle circle: for the   *)
(* pulled squares q j = transform.pull (owners p (roles j)) (transform       *)
(* <true,false,true>, roles 5 9 2), DiagonalWallCenter.point (DWC_POINT)     *)
(* forces owner 5 to contain (2,2); C981DoubleWallElbows.center at placement *)
(* 2 puts (2,2) in owner 7, contradicting owners_disjoint.                   *)
(* Conventions of C981DoubleWallElbows.ml / Bridge_C981Row27.ml (c981br_ toolkit): *)
(* Check v is decided at a literal vector by c981dce_check (the query facts  *)
(* are produced by c981br_in / c981br_out, which fail exactly when the Lean  *)
(* membership decide fails); excludes is a producer at a literal vector.    *)
(* The Lean `fun h => apart 1 2 .. (3,3)` premise is c981br_excl (owner 9   *)
(* misses T(3,3) since owner 2 contains it).  Tag C981DCE_.                  *)
(* ========================================================================= *)

needs "n12/geometry/C981DoubleWallElbows.ml";;
needs "n12/geometry/DiagonalWallCenter.ml";;

(* Lean: transform, roles *)
let C981DCE_TRANSFORM = (true, false, true);;
let C981DCE_ROLES = [5; 9; 2];;

(* Lean: insidePoints, outsidePoints *)
let c981dce_inside_points j =
  match j with
    0 -> [(`&2`, `&113 / &50`); (`&113 / &50`, `&2`); (`&47 / &20`, `&47 / &20`)]
  | 1 -> [(`&1543 / &500`, `&2`); (`&3`, `&12 / &5`); (`&12 / &5`, `&3`)]
  | _ -> [(`&3`, `&3`)];;
let C981DCE_OUTSIDE_POINTS = [(`&47 / &20`, `&33 / &20`); (`&33 / &20`, `&47 / &20`)];;

let C981DCE_SQ = map (fun n -> map (fun f -> mk_var(f ^ n, `:real`)) ["c"; "s"; "u"; "v"; "a"])
                     ["A"; "R"];;

(* DiagonalWallCenter.point for q 0, q 1, stated for the original squares A R *)
(* at the transformed points (the Lean `point` and `original` steps).        *)
let C981DCE_GEOM =
  let t = C981DCE_TRANSFORM in
  let sq j = el j C981DCE_SQ in
  let unit j = let [c; s; _; _; a] = sq j in
               [mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                        (mk_binop `( * ):real->real->real` s s), `&1`);
                mk_binop `(<):real->real->bool` `&0` a] in
  let aa j = last (sq j) in
  let lin j p = c981ttr_lin (sq j) (c981ttr_apply t p) in
  let hyps = unit 0 @ unit 1 @
             [mk_binop `(<):real->real->bool` `&1` (aa 0); mk_eq(aa 0, aa 1);
              mk_binop `(<=):real->real->bool` (aa 1) `&1001 / &1000`;
              list_mk_comb(`lcont`, sq 1)] @
             map (lin 0) (c981dce_inside_points 0) @
             map (fun p -> mk_neg (lin 0 p)) C981DCE_OUTSIDE_POINTS @
             map (lin 1) (c981dce_inside_points 1) @
             [mk_neg (lin 1 (`&3`, `&3`)); list_mk_comb(`ldisj`, sq 0 @ sq 1)] in
  let goal = list_mk_forall(List.concat C981DCE_SQ, mk_imp(list_mk_conj hyps, lin 0 (`&2`, `&2`))) in
  let gth = CONV_RULE REAL_RAT_REDUCE_CONV
              (REWRITE_RULE[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW]
                 (SPECL (List.concat (map (c981ttr_pull t) C981DCE_SQ)) DWC_POINT)) in
  prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC gth THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
    REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW; ldisj] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[LCONT_PULLX; LCONT_PULLY; LCONT_PULLSW] THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* the query facts of Check v (first two conjuncts), plus the derived       *)
(* exclusion of T(3,3) from owner 9 (apart 1 2 with inside 2 (3,3))          *)
let c981dce_facts vtm =
  let t = C981DCE_TRANSFORM in
  let r j = el j C981DCE_ROLES in
  let ins j = map (fun p -> c981br_in vtm (r j) (c981ttr_apply t p)) (c981dce_inside_points j) in
  ins 0 @ map (fun p -> c981br_out vtm (r 0) (c981ttr_apply t p)) C981DCE_OUTSIDE_POINTS @
  ins 1 @ ins 2;;

(* Lean: Check (decided at a literal vector) *)
let c981dce_check vtm =
  (try ignore (c981dce_facts vtm); true with Failure _ -> false) &&
  c981dwe_placement_check vtm 2;;

(* Lean: excludes  (producer at a literal vector; fails iff Check fails) *)
let c981dce_excludes vtm =
  if not (c981dce_check vtm) then failwith "c981dce_excludes: Check fails" else
  let t = C981DCE_TRANSFORM in
  let r0 = 5 and r1 = 9 and r2 = 2 in
  let facts = c981dce_facts vtm @
              [c981br_excl vtm r1 r2 (c981ttr_apply t (`&3`, `&3`)); c981br_apart vtm r0 r1] in
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let side = MATCH_MP OO_SIDE np in
  let per r = let mt = mk_small_numeral (c981br_mask r) in
              [SPEC mt (MATCH_MP OO_UNIT np); SPEC mt (MATCH_MP OO_BOX np)] in
  let fs = map (fun th -> MP (SPEC_ALL th) h) facts in
  let gth = SPECL (List.concat (map c981br_owner [r0; r1])) C981DCE_GEOM in
  let ths = side :: MATCH_MP C981BR_ZERO_LT side :: MATCH_MP OO_SIDE_LE np :: fs @
            per r0 @ per r1 in
  let original = UNDISCH (prove(mk_imp(hyp, list_mk_comb(`linside`, c981br_owner r0 @ [`&2`; `&2`])),
                       DISCH_TAC THEN MP_TAC gth THEN REWRITE_TAC ths)) in
  let other = UNDISCH (SPEC_ALL (c981dwe_center vtm 2)) in
  if not (hd (let (_, rs, _) = C981DWE_PLACEMENTS.(2) in rs) = 7) then failwith "c981dce: placement" else
  let ap = MP (SPEC_ALL (c981br_apart vtm r0 7)) h in
  let contra = REWRITE_RULE[original; other] (SPECL [`&2`; `&2`] (REWRITE_RULE[ldisj] ap)) in
  prove(mk_comb(`c981vd_excludes_vector`, vtm),
    REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> ACCEPT_TAC (MP (DISCH hyp contra) th)));;

(* Lean: representative5_checked, representative6_checked, representative42_checked *)
let C981DCE_REPRESENTATIVES_CHECKED =
  List.for_all (fun i -> c981dce_check (rand (concl (c981br_rep_el i)))) [5; 6; 42];;
if not C981DCE_REPRESENTATIVES_CHECKED then failwith "C981DCE: representative checks fail";;

(* Lean: representative5_excluded *)
let C981DCE_REPRESENTATIVE5_EXCLUDED = c981br_rep_excluded 5 c981dce_excludes;;
(* Lean: representative6_excluded *)
let C981DCE_REPRESENTATIVE6_EXCLUDED = c981br_rep_excluded 6 c981dce_excludes;;
(* Lean: representative42_excluded *)
let C981DCE_REPRESENTATIVE42_EXCLUDED = c981br_rep_excluded 42 c981dce_excludes;;

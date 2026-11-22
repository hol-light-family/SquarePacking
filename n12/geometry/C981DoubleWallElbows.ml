(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981DoubleWallElbows.lean                         *)
(* (namespace N12Compact.C981DoubleWallElbows).  Whole original-vector       *)
(* exclusions using opposite actual elbows; a double auxiliary wall retains  *)
(* its additional strict point and its exact outer missing point.            *)
(* Conventions of C981WallElbows.ml / Bridge_C981Row27.ml (c981br_* toolkit):*)
(* owners p i is the OriginalOwners owner at mask EL i c981ow_masks;         *)
(* ExcludesVector is c981vd_excludes_vector.  A Transform <swap,rx,ry> is an *)
(* OCaml triple handled by c981ttr_apply / c981ttr_pull (C981TwoTipRows.ml). *)
(* c981dwe_geom i is CentralWallCenter.point (CWC_POINT, double = false) or  *)
(* DoubleAuxWallCenter.point (DAWCE_POINT, double = true) for the pulled     *)
(* squares q j = transform.pull (owners p (roles j)), stated for the         *)
(* original squares at the transformed points; its conclusion is            *)
(* linside (owners p (roles 0)) 2 2 (every transform fixes (2,2)), i.e. the  *)
(* Lean `original` step.  PlacementCheck / Check quantify over the computed  *)
(* query point lists; they are decided at a literal vector by the producers  *)
(* c981dwe_placement_check / c981dwe_check, and center / excludes are        *)
(* producers at a literal vector (they fail exactly when the Lean decide     *)
(* would).  Tag C981DWE_.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/C981WallElbows.ml";;
needs "n12/geometry/C981TwoTipRows.ml";;
needs "n12/geometry/DoubleAuxWallCenter.ml";;

(* Lean: Placement, placements  (transform, roles, double) *)
let C981DWE_PLACEMENTS =
  [| ((false, false, true), [5; 10; 9], false);
     ((false, false, true), [5; 10; 9], true);
     ((false, true, false), [7; 8; 11], false);
     ((true, true, false), [7; 11; 8], true) |];;

(* Lean: insidePoints, outsidePoints *)
let c981dwe_inside_points double j =
  match j with
    0 -> [(`&2`, `&113 / &50`); (`&113 / &50`, `&2`); (`&47 / &20`, `&47 / &20`)]
  | 1 -> if double then [(`&1543 / &500`, `&2`); (`&3`, `&12 / &5`); (`&3`, `&87 / &50`)]
         else [(`&1543 / &500`, `&2`); (`&3`, `&12 / &5`)]
  | _ -> [(`&2`, `&1543 / &500`); (`&12 / &5`, `&3`)];;
let c981dwe_outside_points double j =
  match j with
    0 -> [(`&47 / &20`, `&33 / &20`); (`&33 / &20`, `&47 / &20`)]
  | 1 -> if double then [(`&3`, `&8 / &5`)] else [(`&3`, `&87 / &50`)]
  | _ -> [(`&87 / &50`, `&3`)];;

let C981DWE_SQ = map (fun n -> map (fun f -> mk_var(f ^ n, `:real`)) ["c"; "s"; "u"; "v"; "a"])
                     ["A"; "R"; "T"];;

(* ------------------------------------------------------------------------- *)
(* The geometry of one placement (Lean center, the `point` and `original`    *)
(* steps), for the original squares A R T at the transformed points.         *)
(* ------------------------------------------------------------------------- *)

let c981dwe_geom_of (t, double) =
  let sq j = el j C981DWE_SQ in
  let real_eq x y = mk_eq(x, y) in
  let unit j = let [c; s; _; _; a] = sq j in
               [real_eq (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
                          (mk_binop `( * ):real->real->real` s s)) `&1`;
                mk_binop `(<):real->real->bool` `&0` a] in
  let aa j = last (sq j) in
  let ins j = map (fun p -> c981ttr_lin (sq j) (c981ttr_apply t p)) (c981dwe_inside_points double j)
  and outs j = map (fun p -> mk_neg (c981ttr_lin (sq j) (c981ttr_apply t p))) (c981dwe_outside_points double j) in
  let disj i j = list_mk_comb(`ldisj`, sq i @ sq j) in
  let hyps = List.concat (map unit [0; 1; 2]) @
             [mk_binop `(<):real->real->bool` `&1` (aa 0); real_eq (aa 0) (aa 1); real_eq (aa 0) (aa 2);
              list_mk_comb(`lcont`, sq 1); list_mk_comb(`lcont`, sq 2)] @
             List.concat (map (fun j -> ins j @ outs j) [0; 1; 2]) @ [disj 0 1; disj 0 2] in
  let concl0 = c981ttr_lin (sq 0) (c981ttr_apply t (`&2`, `&2`)) in
  let goal = list_mk_forall(List.concat C981DWE_SQ, mk_imp(list_mk_conj hyps, concl0)) in
  let base = if double then DAWCE_POINT else CWC_POINT in
  let gth = CONV_RULE REAL_RAT_REDUCE_CONV
              (REWRITE_RULE[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW]
                 (SPECL (List.concat (map (c981ttr_pull t) C981DWE_SQ)) base)) in
  prove(goal,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC gth THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
    REWRITE_TAC[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW; ldisj] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[LCONT_PULLX; LCONT_PULLY; LCONT_PULLSW] THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* the four placements; i = 0, 2 use CentralWallCenter.point, 1, 3 DoubleAuxWallCenter.point *)
let C981DWE_GEOM =
  Array.map (fun (t, _, d) -> c981dwe_geom_of (t, d)) C981DWE_PLACEMENTS;;

(* ------------------------------------------------------------------------- *)
(* PlacementCheck, center, Check, excludes (producers at a literal vector).  *)
(* ------------------------------------------------------------------------- *)

(* the query facts of PlacementCheck v i *)
let c981dwe_facts vtm i =
  let (t, roles, double) = C981DWE_PLACEMENTS.(i) in
  let ins j = map (fun p -> c981br_in vtm (el j roles) (c981ttr_apply t p)) (c981dwe_inside_points double j) in
  let outs j = map (fun p -> c981br_out vtm (el j roles) (c981ttr_apply t p)) (c981dwe_outside_points double j) in
  ins 0 @ outs 0 @ ins 1 @ outs 1 @ ins 2 @ outs 2;;

(* Lean: PlacementCheck (decided at a literal vector) *)
let c981dwe_placement_check vtm i =
  (try ignore (c981dwe_facts vtm i); true with Failure _ -> false);;

(* Lean: center
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = ccc981ri_family /\
        c981ow_vector c1 c2 a b l = v ==> linside (owners p (roles i 0)) (&2) (&2) *)
let c981dwe_center vtm i =
  let (_, roles, _) = C981DWE_PLACEMENTS.(i) in
  let r0 = el 0 roles and r1 = el 1 roles and r2 = el 2 roles in
  if length (setify roles) < 3 then failwith "c981dwe_center: roles not injective" else
  let facts = c981dwe_facts vtm i @ [c981br_apart vtm r0 r1; c981br_apart vtm r0 r2] in
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let side = MATCH_MP OO_SIDE np in
  let side0 = MATCH_MP C981BR_ZERO_LT side in
  let per r = let mt = mk_small_numeral (c981br_mask r) in
              [SPEC mt (MATCH_MP OO_UNIT np); SPEC mt (MATCH_MP OO_BOX np)] in
  let fs = map (fun th -> MP (SPEC_ALL th) h) facts in
  let gth = SPECL (List.concat (map c981br_owner roles)) C981DWE_GEOM.(i) in
  let ths = side :: side0 :: fs @ List.concat (map per roles) in
  let concl0 = list_mk_comb(`linside`, c981br_owner r0 @ [`&2`; `&2`]) in
  prove(list_mk_forall(C981BR_VARS, mk_imp(hyp, concl0)),
        REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC gth THEN REWRITE_TAC ths);;

(* Lean: placementPairs *)
let C981DWE_PLACEMENT_PAIRS = [(1, 2); (1, 3); (0, 3)];;

(* Lean: Check (decided at a literal vector) *)
let c981dwe_check vtm =
  List.exists (fun (i, j) -> c981dwe_placement_check vtm i && c981dwe_placement_check vtm j)
    C981DWE_PLACEMENT_PAIRS;;

(* Lean: excludes  (the first pair of placementPairs whose checks hold) *)
let c981dwe_excludes vtm =
  let (i, j) =
    try find (fun (i, j) -> c981dwe_placement_check vtm i && c981dwe_placement_check vtm j)
          C981DWE_PLACEMENT_PAIRS
    with Failure _ -> failwith "c981dwe_excludes: Check fails" in
  let ri = let (_, r, _) = C981DWE_PLACEMENTS.(i) in hd r
  and rj = let (_, r, _) = C981DWE_PLACEMENTS.(j) in hd r in
  if ri = rj then failwith "c981dwe_excludes: same centre owner" else
  let ci = c981dwe_center vtm i and cj = c981dwe_center vtm j in
  let ap = c981br_apart vtm ri rj in
  prove(mk_comb(`c981vd_excludes_vector`, vtm),
    REWRITE_TAC[c981vd_excludes_vector] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(UNDISCH (SPEC_ALL ap)) THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&2`; `&2`]) THEN
    REWRITE_TAC[UNDISCH (SPEC_ALL ci); UNDISCH (SPEC_ALL cj)]);;

(* Lean: coveredIds *)
let c981dwe_covered_ids = new_definition
 `c981dwe_covered_ids = [1; 20; 21; 23; 51; 112]`;;
let C981DWE_COVERED = [1; 20; 21; 23; 51; 112];;

(* Lean: covered_count *)
let C981DWE_COVERED_COUNT = prove
 (`LENGTH c981dwe_covered_ids = 6`,
  REWRITE_TAC[c981dwe_covered_ids; LENGTH] THEN CONV_TAC NUM_REDUCE_CONV);;

(* Lean: covered_checked  (Check holds at every covered representative) *)
let C981DWE_COVERED_CHECKED =
  List.for_all (fun i -> c981dwe_check (rand (concl (c981br_rep_el i)))) C981DWE_COVERED;;
if not C981DWE_COVERED_CHECKED then failwith "C981DWE: covered_checked fails";;

(* Lean: covered_excluded *)
let C981DWE_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981dwe_covered_ids]
    (c981br_covered C981DWE_COVERED (map (fun i -> c981br_rep_excluded i c981dwe_excludes) C981DWE_COVERED));;

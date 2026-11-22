(* ========================================================================= *)
(* Phase 2: Compact/Bridge/C981FullAuxNegative.lean                          *)
(* (namespace N12Compact.C981FullAuxNegative).  Shared original C981         *)
(* representatives 3 and 4, in the chart (x,y) = (4-oldY, oldX): the exact   *)
(* right-wall clearance and the full C/B/L support cycle close the vector.   *)
(*                                                                           *)
(* Conventions (C981WallElbows.ml / C981DoubleWallElbows.ml, c981br_ tools):   *)
(* owners p i is the OriginalOwners owner at mask EL i c981ow_masks;         *)
(* ExcludesVector is c981vd_excludes_vector; transform <true,false,true> is  *)
(* the OCaml triple C981FAN_T, chart p i = transform.pull (owners p i) is    *)
(* the 5-tuple c981fan_chart i (pullY then pullSwap of the owner tuple), so  *)
(*   linside (chart i) x y <=> linside (owner i) y (4 - x).                  *)
(* Structure of the port:                                                    *)
(*  * c981fan_ctx q3 q5 q6 q7 q8 q9 q10 q11 l collects, for abstract squares *)
(*    qi (the charts), exactly the facts the Lean proof extracts from        *)
(*    Check v and the packing: OpenSquare invariants, common side l > 1      *)
(*    (side), containment (box), the DataCheck inside / outside points       *)
(*    (input / absent), the PlacementCheck centre (center), the TopCheck     *)
(*    disjunction, and pairwise disjointness (apart).                       *)
(*  * The Lean theorems are proved for abstract squares from c981fan_ctx     *)
(*    (C981FAN_G_ thms), then lifted to the packing (C981FAN_CTX_THM v, a        *)
(*    producer at a literal vector v satisfying Check: |- !c1 c2 a b l.     *)
(*    NPACK .. /\ IMAGE binarysum (FFP ..) = ccc981ri_family /\              *)
(*    c981ow_vector c1 c2 a b l = v ==> c981fan_ctx (chart 3) .. (chart 11) l)*)
(*    by c981fan_* producers whose statements are the Lean ones.            *)
(*  * CanonicalFrame p i (square, side, inside, cosine, canonical) is        *)
(*    c981fan_canonical c s u v a (chart i); EscapingFrame p is              *)
(*    c981fan_escaping c s u v a (chart 5) l; PositiveBounds D B is           *)
(*    c981fan_positive_bounds D B; Normal is c977cc_normal; lower / upper are *)
(*    ABT_lower / ABT_upper.  The OpenSquare invariants of a frame are       *)
(*    explicit conjuncts.                                                    *)
(*  * DataCheck / TopCheck / Check are decided at a literal vector by the    *)
(*    OCaml predicates c981fan_data_check / c981fan_top_check /             *)
(*    c981fan_check (true exactly when every listed query fact is proved).   *)
(* Tag C981FAN_ / c981fan_.                                                  *)
(* ========================================================================= *)

needs "n12/geometry/C981DoubleWallElbows.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/FullAuxWallNegativeCycle.ml";;
needs "n12/geometry/FullAuxWallPositiveCNegativeB.ml";;
needs "n12/geometry/FullAuxWallRightSupport.ml";;
needs "n12/geometry/FullAuxWallSharpClearance.ml";;
needs "n12/geometry/FullAuxWallSmallOffset.ml";;
needs "n12/geometry/FullAuxWallPositiveLowerAngleSupport.ml";;
needs "n12/geometry/FullAuxWallPositiveUpperAngleSupport.ml";;
needs "n12/geometry/FullAuxWallNegativeLeft.ml";;
needs "n12/geometry/FullAuxWallPositiveLeft.ml";;
needs "n12/geometry/SouthwestCentralReach.ml";;
needs "n12/geometry/SteepElbowTopSegment.ml";;
needs "n12/geometry/CentralWallCenter.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/FullAuxWallEscape.ml";;
needs "n12/geometry/FullAuxWallPositiveOpposite.ml";;
needs "n12/geometry/FullAuxWallPositiveAngleOrder.ml";;
needs "n12/geometry/FullAuxWallPositiveReach.ml";;
needs "n12/geometry/FullAuxWallPositiveTransverse.ml";;
needs "n12/geometry/FullAuxWallPositiveTop.ml";;

(* ------------------------------------------------------------------------- *)
(* Data (chart coordinates).                                                 *)
(* ------------------------------------------------------------------------- *)

(* Lean: transform *)
let C981FAN_T = (true, false, true);;

(* Lean: insidePoints, outsidePoints *)
let C981FAN_INSIDE =
  [3, [(`&1`, `&3`)];
   5, [(`&2`, `&113 / &50`); (`&113 / &50`, `&2`); (`&47 / &20`, `&47 / &20`)];
   6, [(`&33 / &20`, `&47 / &20`); (`&1`, `&113 / &50`); (`&1`, `&12 / &5`)];
   7, [(`&33 / &20`, `&33 / &20`); (`&87 / &50`, `&2`); (`&2`, `&87 / &50`)];
   8, [(`&8 / &5`, `&1`)];
   9, [(`&1543 / &500`, `&2`); (`&3`, `&12 / &5`)];
   10, [(`&2`, `&1543 / &500`); (`&8 / &5`, `&3`)];
   11, [(`&457 / &500`, `&2`); (`&1`, `&8 / &5`); (`&1`, `&87 / &50`)]];;
let C981FAN_OUTSIDE =
  [5, [(`&47 / &20`, `&33 / &20`); (`&33 / &20`, `&47 / &20`); (`&12 / &5`, `&3`)];
   7, [(`&47 / &20`, `&47 / &20`); (`&33 / &20`, `&47 / &20`); (`&47 / &20`, `&33 / &20`)];
   9, [(`&3`, `&87 / &50`)]];;
(* Lean: TopCheck (the two alternatives for chart 10) *)
let C981FAN_TOP = [(`&12 / &5`, `&3`); (`&113 / &50`, `&3`)];;

let C981FAN_IDX = [3; 5; 6; 7; 8; 9; 10; 11];;
let c981fan_q i = map (fun f -> mk_var(f ^ string_of_int i, `:real`)) ["c"; "s"; "u"; "v"; "a"];;
let c981fan_lin q (x, y) = list_mk_comb(`linside`, q @ [x; y]);;
let C981FAN_PAIRS =
  List.concat (map (fun i -> map (fun j -> (i, j)) (filter (fun j -> i < j) C981FAN_IDX)) C981FAN_IDX);;

(* ------------------------------------------------------------------------- *)
(* The abstract context.                                                     *)
(* ------------------------------------------------------------------------- *)

(* new_definition, returning the existing definition when the file is re-read *)
let c981fan_define tm =
  try new_definition tm with Failure _ ->
  let f, vs = strip_comb (lhs (snd (strip_forall tm))) in
  let name = fst (dest_var f) in
  let th = find (fun th -> try fst (dest_const (fst (strip_comb (lhs (snd (strip_forall (concl th))))))) = name
                  with Failure _ -> false) (definitions ()) in
  if is_const (lhs (concl th)) then GENL vs (RIGHT_BETAS vs th) else th;;

let C981FAN_ARGS = List.concat (map c981fan_q C981FAN_IDX) @ [`l:real`];;

let c981fan_ctx =
  let per i = let q = c981fan_q i in
    let c = el 0 q and s = el 1 q and a = el 4 q in
    [mk_eq(mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c c)
             (mk_binop `( * ):real->real->real` s s), `&1`);
     mk_binop `(<):real->real->bool` `&0` a; mk_eq(a, `l:real`); list_mk_comb(`lcont`, q)] in
  let ins = List.concat (map (fun (i, ps) -> map (c981fan_lin (c981fan_q i)) ps) C981FAN_INSIDE)
  and fan_outs = List.concat (map (fun (i, ps) -> map (fun p -> mk_neg (c981fan_lin (c981fan_q i) p)) ps)
                           C981FAN_OUTSIDE) in
  let centre = c981fan_lin (c981fan_q 7) (`&2`, `&2`) in
  let top = list_mk_disj (map (c981fan_lin (c981fan_q 10)) C981FAN_TOP) in
  let aparts = map (fun (i, j) -> list_mk_comb(`ldisj`, c981fan_q i @ c981fan_q j)) C981FAN_PAIRS in
  let body = list_mk_conj (List.concat (map per C981FAN_IDX) @ [`&1 < l`] @ ins @ fan_outs @
                           [centre; top] @ aparts) in
  let cty = itlist (fun v ty -> mk_fun_ty (type_of v) ty) C981FAN_ARGS `:bool` in
  c981fan_define (mk_eq(list_mk_comb(mk_var("c981fan_ctx", cty), C981FAN_ARGS), body));;

let C981FAN_CTX_TM = lhs (snd (strip_forall (concl c981fan_ctx)));;

(* Lean: CanonicalFrame p i (for the square q = chart p i) *)
let c981fan_canonical = c981fan_define
 `c981fan_canonical c s u v a (cq:real) sq uq vq aq <=>
    c * c + s * s = &1 /\ &0 < a /\ a = aq /\
    (forall x y. linside c s u v a x y <=> linside cq sq uq vq aq x y) /\
    &0 < c /\ abs s <= c`;;

(* Lean: EscapingFrame p (q = chart p 5, l = p.commonSide) *)
let c981fan_escaping = c981fan_define
 `c981fan_escaping c s u v a (cq:real) sq uq vq aq (l:real) <=>
    c * c + s * s = &1 /\ &0 < a /\ a = l /\
    (forall x y. linside c s u v a x y <=> linside cq sq uq vq aq x y) /\
    c977cc_normal c s /\ &0 < s /\ &4 * s <= c /\ &2 * (c + s) <= u /\
    linside c s u v a (&2) (&113 / &50) /\ linside c s u v a (&47 / &20) (&47 / &20) /\
    linside c s u v a (&5 / &2) (&3) /\
    v + a <= &3 * c - (&12 / &5) * s /\
    u - &2 * (c + s) < s pow 2 / &5 /\
    c * (u - &2 * (c + s)) + (&2 / &5) * s pow 2 - (&1 - c) * (&1 - s) < &0 /\
    u - &2 * (c + s) < s pow 2 / &10`;;

(* Lean: PositiveBounds D B *)
let c981fan_positive_bounds = c981fan_define
 `c981fan_positive_bounds cD sD uD vD aD cB sB uB vB aB <=>
    c977cc_normal cD sD /\ c977cc_normal cB sB /\ aD = aB /\ &1 < aD /\
    linside cD sD uD vD aD (&2) (&2) /\ linside cD sD uD vD aD (&33 / &20) (&33 / &20) /\
    linside cD sD uD vD aD (&2) (&3 / &2) /\ linside cD sD uD vD aD (&6 / &5) (&19 / &10) /\
    cD - (&8 / &5) * sD <= vD /\
    linside cB sB uB vB aB (&33 / &20) (&47 / &20) /\ linside cB sB uB vB aB (&1) (&113 / &50) /\
    linside cB sB uB vB aB (&1) (&12 / &5) /\
    uB + aB <= (&8 / &5) * cB + &3 * sB /\ vB + aB <= &3 * cB - sB /\
    (&457 / &500) * cB + &2 * sB <= uB /\ &3 / &10 < sB /\
    &1 < (&343 / &500) * cB + sB /\ sD * cB < cD * sB /\
    (vD + aD <= ABT_lower cB sB uB vB aB (--sD) cD \/
     ABT_upper cD sD uD vD aD (--sB) cB <= vB) /\
    uD + aD - &2 * (cD + sD) < &1 / &1000 /\ &1 / &20 < sD /\
    &50 * sD < &11 * cD /\ sB < &23 / &50`;;

(* ------------------------------------------------------------------------- *)
(* Tools for the abstract proofs.                                            *)
(* ------------------------------------------------------------------------- *)

let C981FAN_LDISJ_SYM = prove
 (`forall cA sA uA vA aA cB sB uB vB aB. ldisj cA sA uA vA aA cB sB uB vB aB
     ==> ldisj cB sB uB vB aB cA sA uA vA aA`,
  REWRITE_TAC[ldisj] THEN MESON_TAC[]);;

let C981FAN_PULLS = [LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW];;

(* the pulled 5-tuples, read off the LINSIDE_PULL* patterns *)
let c981fan_pull th q =
  let l = lhs (snd (strip_forall (concl (SPECL q th)))) in
  let args = snd (strip_comb l) in
  [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args];;
let c981fan_px = c981fan_pull LINSIDE_PULLX;;
let c981fan_py = c981fan_pull LINSIDE_PULLY;;
let c981fan_psw = c981fan_pull LINSIDE_PULLSW;;

let c981fan_is_ldisj t = try fst (dest_const (fst (strip_comb t))) = "ldisj" with Failure _ -> false;;
let c981fan_is_lcont t = try fst (dest_const (fst (strip_comb t))) = "lcont" with Failure _ -> false;;
let c981fan_is_frame_eq t =
  try let _, b = strip_forall t in
      let p, q = dest_iff b in
      fst (dest_const (fst (strip_comb p))) = "linside" &&
      fst (dest_const (fst (strip_comb q))) = "linside" && length (fst (strip_forall t)) = 2
  with Failure _ -> false;;
let c981fan_eqs asl = map snd (filter (fun (_, th) -> c981fan_is_frame_eq (concl th)) asl);;

(* goal ~linside q x y, from ldisj q r (either order) and linside r x y *)
let C981FAN_OUT_TAC (asl, w as g) =
  let p = dest_neg w in
  let args = snd (strip_comb p) in
  let q = [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args] and xy = [el 5 args; el 6 args] in
  let try_one (_, th) =
    let t = concl th in
    if not (c981fan_is_ldisj t) then failwith "" else
    let a = snd (strip_comb t) in
    let q1 = [el 0 a; el 1 a; el 2 a; el 3 a; el 4 a] and q2 = [el 5 a; el 6 a; el 7 a; el 8 a; el 9 a] in
    let other = if q1 = q then q2 else if q2 = q then q1 else failwith "" in
    let oth = find (fun (_, h) -> concl h = list_mk_comb(`linside`, other @ xy)) asl in
    let d = SPECL xy (REWRITE_RULE[ldisj] th) in
    (MP_TAC d THEN MP_TAC (snd oth) THEN CONV_TAC TAUT) g in
  tryfind try_one asl;;

let C981FAN_LDISJ_TAC (asl, w as g) =
  if not (c981fan_is_ldisj w) then failwith "C981FAN_LDISJ_TAC" else
  (REWRITE_TAC(ldisj :: C981FAN_PULLS @ c981fan_eqs asl) THEN REPEAT GEN_TAC THEN
   FIRST_ASSUM(fun th -> if c981fan_is_ldisj (concl th)
                         then MATCH_ACCEPT_TAC (REWRITE_RULE[ldisj] th) else NO_TAC)) g;;

let C981FAN_LCONT_TAC (asl, w as g) =
  if not (c981fan_is_lcont w) then failwith "C981FAN_LCONT_TAC" else
  (REPEAT (MATCH_MP_TAC LCONT_PULLX ORELSE MATCH_MP_TAC LCONT_PULLY ORELSE
           MATCH_MP_TAC LCONT_PULLSW) THEN
   (FIRST_ASSUM ACCEPT_TAC ORELSE
    (W(fun (asl, _) -> REWRITE_TAC(lcont :: c981fan_eqs asl)) THEN
     FIRST_ASSUM(fun th -> if c981fan_is_lcont (concl th)
                           then ACCEPT_TAC (REWRITE_RULE[lcont] th) else NO_TAC)))) g;;

let C981FAN_EQ_TAC (asl, w as g) =
  if not (is_eq w) then failwith "C981FAN_EQ_TAC" else
  (CONV_TAC REAL_RING ORELSE
   FIRST_ASSUM(fun th -> if is_eq (concl th) && type_of (lhs (concl th)) = `:real`
                         then MP_TAC th THEN CONV_TAC REAL_RING else NO_TAC)) g;;

let C981FAN_ARITH_TAC = C981FAN_EQ_TAC ORELSE NLIN_TAC ~deg2:false [];;

(* a goal linside q x y from a frame fact linside F x y, F equivalent to q *)
let C981FAN_FRAME_FACT_TAC (asl, w as g) =
  let eqs = c981fan_eqs asl in
  if eqs = [] then failwith "C981FAN_FRAME_FACT_TAC" else
  let cands = filter (fun (_, th) -> let t = concl th in
                 (try fst (dest_const (fst (strip_comb (if is_neg t then dest_neg t else t)))) = "linside"
                  with Failure _ -> false)) asl in
  tryfind (fun (_, th) -> let th' = REWRITE_RULE eqs th in
                          if concl th' = w then ACCEPT_TAC th' g else failwith "") cands;;

let C981FAN_ATOM_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC; C981FAN_FRAME_FACT_TAC; REWRITE_TAC[] THEN NO_TAC; C981FAN_LDISJ_TAC; C981FAN_LCONT_TAC;
         C981FAN_OUT_TAC;
         REWRITE_TAC[c977cc_normal] THEN REPEAT CONJ_TAC THEN
           (FIRST_ASSUM ACCEPT_TAC ORELSE C981FAN_ARITH_TAC);
         C981FAN_ARITH_TAC];;

let C981FAN_ANTS_TAC = REPEAT CONJ_TAC THEN C981FAN_ATOM_TAC;;

let C981FAN_PREP th tuples =
  MP_TAC (SPECL (List.concat tuples) th) THEN
  W(fun (asl, _) -> CONV_TAC (LAND_CONV (BINOP_CONV
      (REWRITE_CONV(C981FAN_PULLS @ c981fan_eqs asl) THENC REAL_RAT_REDUCE_CONV))));;

(* apply a geometry theorem to the given 5-tuples (and scalars); its conclusion
   conjuncts become assumptions *)
let C981FAN_APPLY th tuples =
  C981FAN_PREP th tuples THEN ANTS_TAC THENL
  [C981FAN_ANTS_TAC; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))];;

(* apply a geometry theorem with conclusion F *)
let C981FAN_CLOSE th tuples =
  C981FAN_PREP th tuples THEN ANTS_TAC THENL [C981FAN_ANTS_TAC; REWRITE_TAC[]];;

(* a fact proved by the atom tactic *)
let C981FAN_HAVE tm = SUBGOAL_THEN tm ASSUME_TAC THENL [C981FAN_ATOM_TAC; ALL_TAC];;

let C981FAN_SUBST_TAC =
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let t = concl th in is_eq t && is_var (lhs t) && is_var (rhs t) &&
                        type_of (lhs t) = `:real` && rhs t = `l:real`)));;

(* unfold an assumption c981fan_ctx .. (kept), substitute the sides, add symmetric ldisj *)
let C981FAN_UNFOLD_TAC =
  FIRST_ASSUM(fun th -> if fst (strip_comb (concl th)) = fst (strip_comb C981FAN_CTX_TM)
                          then MAP_EVERY ASSUME_TAC (CONJUNCTS (REWRITE_RULE[c981fan_ctx] th))
                          else NO_TAC) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    let t = concl th in is_eq t && is_var (lhs t) && is_var (rhs t) &&
                        type_of (lhs t) = `:real` && rhs t = `l:real`))) THEN
  W(fun (asl, _) -> MAP_EVERY (fun (_, th) ->
      if c981fan_is_ldisj (concl th) then ASSUME_TAC (MATCH_MP C981FAN_LDISJ_SYM th) else ALL_TAC) asl);;

let C981FAN_CTX_HYP = C981FAN_CTX_TM;;
let c981fan_goal tm = list_mk_forall(C981FAN_ARGS, mk_imp(C981FAN_CTX_TM, tm));;

let C981FAN_A = [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`];;
let C981FAN_D = [`cD:real`; `sD:real`; `uD:real`; `vD:real`; `aD:real`];;
let C981FAN_B = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;
let C981FAN_LL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`];;
let C981FAN_Q i = c981fan_q i;;
let c981fan_ql i = match c981fan_q i with [c; s; u; v; _] -> [c; s; u; v; `l:real`] | _ -> failwith "ql";;
let c981fan_fl q = match q with [c; s; u; v; _] -> [c; s; u; v; `l:real`] | _ -> failwith "fl";;

(* ------------------------------------------------------------------------- *)
(* Abstract geometry (the Lean proofs, for the chart squares q3 .. q11).     *)
(* ------------------------------------------------------------------------- *)

(* Lean: bottom (private) *)
let C981FAN_G_BOTTOM = prove
 (c981fan_goal `linside c7 s7 u7 v7 a7 (&2) (&3 / &2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C981FAN_UNFOLD_TAC THEN
  C981FAN_APPLY WLR_POINT [c981fan_py (c981fan_ql 11)] THEN
  SUBGOAL_THEN `linside c11 s11 u11 v11 l (&1) (&3 / &2)` ASSUME_TAC THENL
  [MAP_EVERY UNDISCH_TAC [`linside c11 s11 u11 v11 l (&1) (&36 / &25)`;
                          `linside c11 s11 u11 v11 l (&1) (&8 / &5)`] THEN
   REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  C981FAN_APPLY SWCR_NORTHEAST [c981fan_px (c981fan_py (c981fan_ql 7))] THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* unfold every assumption whose head constant is name (a predicate definition) *)
let C981FAN_UNPRED_TAC defth name =
  REPEAT(FIRST_X_ASSUM(fun th ->
           if (try fst (dest_const (fst (strip_comb (concl th)))) = name with Failure _ -> false)
           then MAP_EVERY ASSUME_TAC (CONJUNCTS (REWRITE_RULE[defth; REAL_ABS_BOUNDS] th))
           else NO_TAC)) THEN
  C981FAN_SUBST_TAC;;

let C981FAN_UNFRAMES_TAC =
  C981FAN_UNPRED_TAC c981fan_escaping "c981fan_escaping" THEN
  C981FAN_UNPRED_TAC c981fan_canonical "c981fan_canonical";;

(* Lean: canonical_exists (for an abstract OpenSquare) *)
let C981FAN_CANONICAL_EXISTS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c981fan_canonical c' s' u' v' a' c s u v a`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP CLF_CANONICAL_FRAME) THEN
  REWRITE_TAC[c981fan_canonical] THEN MESON_TAC[]);;

let C981FAN_OBTAIN_TAC i names =
  MP_TAC(SPECL (c981fan_ql i) C981FAN_CANONICAL_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC names THEN DISCH_TAC;;

let C981FAN_BOUNDS_TAC c s =
  SUBGOAL_THEN (list_mk_comb(`c977cc_normal`, [c; s])) (STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS)
  THENL [C981FAN_ATOM_TAC; ALL_TAC];;

let C981FAN_A_L = c981fan_fl C981FAN_A and C981FAN_D_L = c981fan_fl C981FAN_D
and C981FAN_B_L = c981fan_fl C981FAN_B and C981FAN_LL_L = c981fan_fl C981FAN_LL;;

(* Lean: escaping_exists *)
let C981FAN_G_ESCAPING = prove
 (c981fan_goal `exists cA sA uA vA aA. c981fan_escaping cA sA uA vA aA c5 s5 u5 v5 a5 l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C981FAN_UNFOLD_TAC THEN
  MP_TAC(SPECL (c981fan_ql 5) CLF_POSITIVE_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC C981FAN_A THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN C981FAN_SUBST_TAC THEN
  C981FAN_APPLY CWC_RIGHT_HIGH [c981fan_ql 9] THEN
  SUBGOAL_THEN `sA <= cA` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj (concl th))) THENL
   [C981FAN_APPLY CWC_SHALLOW [c981fan_psw C981FAN_A_L; c981fan_psw (c981fan_ql 10)] THEN
    C981FAN_HAVE `~linside c5 s5 u5 v5 l (&2) (&2)` THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> concl th = `~linside c5 s5 u5 v5 l (&2) (&2)`)) THEN
    ASM_REWRITE_TAC[];
    C981FAN_CLOSE SETS_IMPOSSIBLE [C981FAN_A_L; c981fan_ql 10]];
   ALL_TAC] THEN
  C981FAN_APPLY FAWE_NARROW_FACES_OF_MISSING [C981FAN_A_L; c981fan_ql 9] THEN
  C981FAN_APPLY FAWRS_ORIGINAL_BOUNDS_OF_MISSING [C981FAN_A_L; c981fan_ql 9] THEN
  C981FAN_APPLY FAWRS_QUADRATIC_OF_CLEARANCE [[`cA:real`; `sA:real`; `uA - &2 * (cA + sA)`]] THEN
  MAP_EVERY EXISTS_TAC C981FAN_A_L THEN
  W(fun (asl, _) -> REWRITE_TAC(c981fan_escaping :: c981fan_eqs asl)) THEN
  C981FAN_ANTS_TAC);;

let C981FAN_ESCAPE_TAC =
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C981FAN_G_BOTTOM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C981FAN_G_ESCAPING);;

(* Lean: negative_frame_impossible *)
let C981FAN_G_NEGATIVE_FRAME_IMPOSSIBLE = prove
 (c981fan_goal `forall cD sD uD vD aD. c981fan_canonical cD sD uD vD aD c7 s7 u7 v7 a7 /\ sD <= &0 ==> false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981FAN_ESCAPE_TAC THEN C981FAN_UNFOLD_TAC THEN C981FAN_UNFRAMES_TAC THEN
  C981FAN_OBTAIN_TAC 6 C981FAN_B THEN C981FAN_UNFRAMES_TAC THEN
  C981FAN_CLOSE FAWNC_NEGATIVE_OPPOSITE_IMPOSSIBLE
    [C981FAN_A_L; C981FAN_D_L; C981FAN_B_L; [`--sD`]]);;

(* Lean: positive_residual *)
let C981FAN_G_POSITIVE_RESIDUAL = prove
 (c981fan_goal `forall cD sD uD vD aD. c981fan_canonical cD sD uD vD aD c7 s7 u7 v7 a7 ==> &0 < sD`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL C981FAN_D o MATCH_MP C981FAN_G_NEGATIVE_FRAME_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: negative_upper_frame_impossible *)
let C981FAN_G_NEGATIVE_UPPER_FRAME_IMPOSSIBLE = prove
 (c981fan_goal `forall cD sD uD vD aD cB sB uB vB aB.
     c981fan_canonical cD sD uD vD aD c7 s7 u7 v7 a7 /\
     c981fan_canonical cB sB uB vB aB c6 s6 u6 v6 a6 /\ sB <= &0 ==> false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981FAN_ESCAPE_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL C981FAN_D o MATCH_MP C981FAN_G_POSITIVE_RESIDUAL) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  C981FAN_UNFOLD_TAC THEN C981FAN_UNFRAMES_TAC THEN
  C981FAN_CLOSE FAWPCN_IMPOSSIBLE [C981FAN_A_L; C981FAN_D_L; C981FAN_B_L; [`--sB`]]);;

(* Lean: upper_positive_residual *)
let C981FAN_G_UPPER_POSITIVE_RESIDUAL = prove
 (c981fan_goal `forall cB sB uB vB aB. c981fan_canonical cB sB uB vB aB c6 s6 u6 v6 a6 ==> &0 < sB`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C981FAN_UNFOLD_TAC THEN C981FAN_OBTAIN_TAC 7 C981FAN_D THEN
  FIRST_ASSUM(MP_TAC o SPECL (C981FAN_D @ C981FAN_B) o
              MATCH_MP C981FAN_G_NEGATIVE_UPPER_FRAME_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive_bounds *)
let C981FAN_G_POSITIVE_BOUNDS = prove
 (c981fan_goal `forall cD sD uD vD aD cB sB uB vB aB.
     c981fan_canonical cD sD uD vD aD c7 s7 u7 v7 a7 /\
     c981fan_canonical cB sB uB vB aB c6 s6 u6 v6 a6
     ==> c981fan_positive_bounds cD sD uD vD aD cB sB uB vB aB`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981FAN_ESCAPE_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL C981FAN_D o MATCH_MP C981FAN_G_POSITIVE_RESIDUAL) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL C981FAN_B o MATCH_MP C981FAN_G_UPPER_POSITIVE_RESIDUAL) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  C981FAN_UNFOLD_TAC THEN C981FAN_UNFRAMES_TAC THEN
  C981FAN_BOUNDS_TAC `cD:real` `sD:real` THEN
  C981FAN_APPLY FAWPO_ALTERNATIVES [C981FAN_A_L; C981FAN_D_L] THEN
  C981FAN_APPLY FAWPAO_PROJECTED_EXCESS [C981FAN_A_L; C981FAN_D_L] THEN
  C981FAN_APPLY FAWSC_OPPOSITE_SLOPE [C981FAN_A_L; C981FAN_D_L] THEN
  C981FAN_HAVE `&25 * sD <= &9 * cD` THEN
  C981FAN_APPLY FAWSC_EXCESS [[`cA:real`; `sA:real`; `uA - &2 * (cA + sA)`]] THEN
  C981FAN_APPLY FAWSO_OFFSET [[`cA:real`; `sA:real`; `cD:real`; `sD:real`;
                               `uA - &2 * (cA + sA)`; `uD + l - &2 * (cD + sD)`]] THEN
  C981FAN_HAVE `uD + l - &2 * (cD + sD) < &1 / &10` THEN
  C981FAN_APPLY FAWPR_BOTTOM_U [C981FAN_A_L; C981FAN_D_L] THEN
  C981FAN_APPLY FAWPR_BOTTOM_FACE [C981FAN_D_L] THEN
  C981FAN_APPLY FAWPR_POINT [C981FAN_D_L] THEN
  C981FAN_APPLY FAWPT_ALTERNATIVES [C981FAN_D_L; C981FAN_B_L] THEN
  C981FAN_APPLY FAWPTP_FACES [C981FAN_D_L; C981FAN_B_L] THEN
  C981FAN_HAVE `&1 < (&343 / &500) * cB + sB` THEN
  C981FAN_APPLY FAWPAO_ORDERED [[`cD:real`; `sD:real`; `cB:real`; `sB:real`]] THEN
  C981FAN_APPLY FAWPLAS_SINE [C981FAN_D_L; C981FAN_B_L] THEN
  C981FAN_APPLY FAWPUAS_SINE [C981FAN_D_L; C981FAN_B_L] THEN
  W(fun (asl, _) -> REWRITE_TAC(c981fan_positive_bounds :: c981fan_eqs asl)) THEN
  C981FAN_ANTS_TAC);;

let C981FAN_LEFT_SETUP_TAC =
  C981FAN_UNFOLD_TAC THEN C981FAN_OBTAIN_TAC 7 C981FAN_D THEN C981FAN_OBTAIN_TAC 6 C981FAN_B THEN
  FIRST_ASSUM(MP_TAC o SPECL (C981FAN_D @ C981FAN_B) o MATCH_MP C981FAN_G_POSITIVE_BOUNDS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  C981FAN_UNPRED_TAC c981fan_positive_bounds "c981fan_positive_bounds" THEN
  C981FAN_UNFRAMES_TAC THEN C981FAN_BOUNDS_TAC `cD:real` `sD:real`;;

(* Lean: negative_left_frame_impossible *)
let C981FAN_G_NEGATIVE_LEFT_FRAME_IMPOSSIBLE = prove
 (c981fan_goal `forall cL sL uL vL aL. c981fan_canonical cL sL uL vL aL c11 s11 u11 v11 a11 /\ sL <= &0 ==> false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981FAN_LEFT_SETUP_TAC THEN
  C981FAN_CLOSE FAWNL_IMPOSSIBLE [C981FAN_LL_L; C981FAN_D_L; C981FAN_B_L; [`--sL`]]);;

(* Lean: left_positive_residual *)
let C981FAN_G_LEFT_POSITIVE_RESIDUAL = prove
 (c981fan_goal `forall cL sL uL vL aL. c981fan_canonical cL sL uL vL aL c11 s11 u11 v11 a11 ==> &0 < sL`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL C981FAN_LL o MATCH_MP C981FAN_G_NEGATIVE_LEFT_FRAME_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: positive_left_frame_impossible *)
let C981FAN_G_POSITIVE_LEFT_FRAME_IMPOSSIBLE = prove
 (c981fan_goal `forall cL sL uL vL aL. c981fan_canonical cL sL uL vL aL c11 s11 u11 v11 a11 /\ &0 <= sL ==> false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  C981FAN_LEFT_SETUP_TAC THEN
  C981FAN_CLOSE FAWPL_IMPOSSIBLE [C981FAN_LL_L; C981FAN_D_L; C981FAN_B_L]);;

(* Lean: excludes (abstract part) *)
let C981FAN_G_EXCLUDES = prove
 (c981fan_goal `false`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  C981FAN_UNFOLD_TAC THEN C981FAN_OBTAIN_TAC 11 C981FAN_LL THEN
  FIRST_ASSUM(MP_TAC o SPECL C981FAN_LL o MATCH_MP C981FAN_G_LEFT_POSITIVE_RESIDUAL) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL C981FAN_LL o MATCH_MP C981FAN_G_POSITIVE_LEFT_FRAME_IMPOSSIBLE) THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* The packing level.                                                        *)
(* ------------------------------------------------------------------------- *)

let C981FAN_LDISJ_PULLSW = prove
 (`forall cA sA uA vA aA cB sB uB vB aB. ldisj cA sA uA vA aA cB sB uB vB aB
     ==> ldisj sA cA uA (--vA - aA) aA sB cB uB (--vB - aB) aB`,
  REWRITE_TAC[ldisj; LINSIDE_PULLSW] THEN MESON_TAC[]);;

(* Lean: chart p i = transform.pull (owners p i) *)
let c981fan_chart i = c981ttr_pull C981FAN_T (c981br_owner i);;

let c981fan_orig p = c981ttr_apply C981FAN_T p;;

(* Lean: input / absent (query facts of DataCheck at the chart points) *)
let c981fan_in vtm i p = c981br_in vtm i (c981fan_orig p);;
let c981fan_out vtm i p = c981br_out vtm i (c981fan_orig p);;

let c981fan_ok f = try ignore (f ()); true with Failure _ -> false;;

(* Lean: DataCheck (decided at a literal vector) *)
let c981fan_data_check vtm =
  List.for_all (fun (i, ps) -> List.for_all (fun p -> c981fan_ok (fun () -> c981fan_in vtm i p)) ps)
    C981FAN_INSIDE &&
  List.for_all (fun (i, ps) -> List.for_all (fun p -> c981fan_ok (fun () -> c981fan_out vtm i p)) ps)
    C981FAN_OUTSIDE;;

(* Lean: TopCheck (decided at a literal vector) *)
let c981fan_top_check vtm =
  List.exists (fun p -> c981fan_ok (fun () -> c981fan_in vtm 10 p)) C981FAN_TOP;;

(* Lean: Check  (DataCheck, C981DoubleWallElbows.PlacementCheck v 2, TopCheck) *)
let c981fan_check vtm =
  c981fan_data_check vtm && c981dwe_placement_check vtm 2 && c981fan_top_check vtm;;

(* |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = ccc981ri_family /\
        c981ow_vector c1 c2 a b l = v ==> c981fan_ctx (chart 3) .. (chart 11) l
   (Lean: side, box, apart, input, absent, center and checked.2.2 together) *)
let C981FAN_CTX_CACHE = ref ([] : (term * thm) list);;
let c981fan_ctx_thm vtm =
  try assoc vtm !C981FAN_CTX_CACHE with Failure _ ->
  let hyp = C981BR_HYP vtm in
  let h = ASSUME hyp in
  let np = CONJUNCT1 h in
  let use th = MP (SPEC_ALL th) h in
  let ins = List.concat (map (fun (i, ps) -> map (fun p -> use (c981fan_in vtm i p)) ps) C981FAN_INSIDE)
  and fan_outs = List.concat (map (fun (i, ps) -> map (fun p -> use (c981fan_out vtm i p)) ps) C981FAN_OUTSIDE) in
  let centre = use (c981dwe_center vtm 2) in
  let top = use (tryfind (fun p -> c981fan_in vtm 10 p) C981FAN_TOP) in
  let aparts = map (fun (i, j) -> use (c981br_apart vtm i j)) C981FAN_PAIRS in
  let mt i = mk_small_numeral (c981br_mask i) in
  let units = map (fun i -> SPEC (mt i) (MATCH_MP OO_UNIT np)) C981FAN_IDX
  and fan_boxes = map (fun i -> SPEC (mt i) (MATCH_MP OO_BOX np)) C981FAN_IDX
  and fan_side = MATCH_MP OO_SIDE np in
  let side0 = MATCH_MP C981BR_ZERO_LT fan_side in
  let facts = fan_side :: side0 :: centre :: ins @ fan_outs @ aparts in
  let goal = list_mk_comb(fst (strip_comb C981FAN_CTX_TM),
                          List.concat (map c981fan_chart C981FAN_IDX) @ [`l:real`]) in
  let th = prove(mk_imp(hyp, goal),
    DISCH_TAC THEN REWRITE_TAC[c981fan_ctx] THEN
    CONV_TAC(REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLY] THENC REAL_RAT_REDUCE_CONV) THEN
    REPEAT CONJ_TAC THEN
    FIRST [MAP_FIRST ACCEPT_TAC facts;
           (DISJ1_TAC THEN ACCEPT_TAC top) ORELSE (DISJ2_TAC THEN ACCEPT_TAC top);
           MATCH_MP_TAC LCONT_PULLSW THEN MATCH_MP_TAC LCONT_PULLY THEN MAP_FIRST ACCEPT_TAC fan_boxes;
           MATCH_MP_TAC C981FAN_LDISJ_PULLSW THEN MATCH_MP_TAC C981WE_LDISJ_PULLY THEN
             MAP_FIRST ACCEPT_TAC aparts;
           MAP_FIRST (fun u -> MP_TAC u THEN CONV_TAC REAL_RING) units]) in
  let r = GENL C981BR_VARS th in
  C981FAN_CTX_CACHE := (vtm, r) :: !C981FAN_CTX_CACHE; r;;

(* lift an abstract theorem  !q.. l. c981fan_ctx q.. l ==> P  to the charts of the packing *)
let c981fan_lift gth vtm =
  let hyp = C981BR_HYP vtm in
  let c = MP (SPEC_ALL (c981fan_ctx_thm vtm)) (ASSUME hyp) in
  GENL C981BR_VARS (DISCH hyp (MATCH_MP gth c));;

(* Lean: canonical_exists  (i : Fin 12 is the mask EL i c981ow_masks) *)
let C981FAN_CANONICAL_EXISTS_PACKING =
  let mi = `EL i c981ow_masks` in
  let owner = map (fun f -> list_mk_comb(f, C981BR_VARS @ [mi])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`] in
  let q = c981ttr_pull C981FAN_T owner in
  let vs = [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] in
  let goal = list_mk_forall(C981BR_VARS @ [`i:num`],
               mk_imp(`NPACK c1 c2 a b l`,
                      list_mk_exists(vs, list_mk_comb(`c981fan_canonical`, vs @ q)))) in
  prove(goal,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC C981FAN_CANONICAL_EXISTS THEN
    FIRST_ASSUM(ASSUME_TAC o SPEC mi o MATCH_MP OO_UNIT) THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OO_SIDE) THEN
    CONJ_TAC THENL [POP_ASSUM(K ALL_TAC) THEN POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING;
                    POP_ASSUM MP_TAC THEN REAL_ARITH_TAC]);;

(* Lean: center (private): linside (chart p 7) 2 2 *)
let c981fan_center vtm =
  let hyp = C981BR_HYP vtm in
  let th = MP (SPEC_ALL (c981dwe_center vtm 2)) (ASSUME hyp) in
  let goal = c981fan_lin (c981fan_chart 7) (`&2`, `&2`) in
  GENL C981BR_VARS (prove(mk_imp(hyp, goal),
    DISCH_TAC THEN
    CONV_TAC(REWRITE_CONV[LINSIDE_PULLSW; LINSIDE_PULLY] THENC REAL_RAT_REDUCE_CONV) THEN
    ACCEPT_TAC th));;

(* Lean: bottom (private) *)
let c981fan_bottom = c981fan_lift C981FAN_G_BOTTOM;;
(* Lean: escaping_exists *)
let c981fan_escaping_exists = c981fan_lift C981FAN_G_ESCAPING;;
(* Lean: negative_frame_impossible *)
let c981fan_negative_frame_impossible = c981fan_lift C981FAN_G_NEGATIVE_FRAME_IMPOSSIBLE;;
(* Lean: positive_residual *)
let c981fan_positive_residual = c981fan_lift C981FAN_G_POSITIVE_RESIDUAL;;
(* Lean: negative_upper_frame_impossible *)
let c981fan_negative_upper_frame_impossible = c981fan_lift C981FAN_G_NEGATIVE_UPPER_FRAME_IMPOSSIBLE;;
(* Lean: upper_positive_residual *)
let c981fan_upper_positive_residual = c981fan_lift C981FAN_G_UPPER_POSITIVE_RESIDUAL;;
(* Lean: positive_bounds *)
let c981fan_positive_bounds_thm = c981fan_lift C981FAN_G_POSITIVE_BOUNDS;;
(* Lean: negative_left_frame_impossible *)
let c981fan_negative_left_frame_impossible = c981fan_lift C981FAN_G_NEGATIVE_LEFT_FRAME_IMPOSSIBLE;;
(* Lean: left_positive_residual *)
let c981fan_left_positive_residual = c981fan_lift C981FAN_G_LEFT_POSITIVE_RESIDUAL;;
(* Lean: positive_left_frame_impossible *)
let c981fan_positive_left_frame_impossible = c981fan_lift C981FAN_G_POSITIVE_LEFT_FRAME_IMPOSSIBLE;;

(* Lean: excludes  |- c981vd_excludes_vector v  (fails unless Check v) *)
let c981fan_excludes vtm =
  if not (c981fan_check vtm) then failwith "c981fan_excludes: Check fails" else
  let th = c981fan_lift C981FAN_G_EXCLUDES vtm in
  EQ_MP (SYM (SPEC vtm c981vd_excludes_vector)) th;;

(* Lean: data_checked, center_checked, representative3_checked, representative4_checked *)
let C981FAN_REP3 = rand (concl (c981br_rep_el 3)) and C981FAN_REP4 = rand (concl (c981br_rep_el 4));;
let C981FAN_DATA_CHECKED = c981fan_data_check C981FAN_REP4;;
let C981FAN_CENTER_CHECKED = c981dwe_placement_check C981FAN_REP4 2;;
let C981FAN_REPRESENTATIVE3_CHECKED = c981fan_check C981FAN_REP3;;
let C981FAN_REPRESENTATIVE4_CHECKED = c981fan_check C981FAN_REP4;;
if not (C981FAN_DATA_CHECKED && C981FAN_CENTER_CHECKED && C981FAN_REPRESENTATIVE3_CHECKED &&
        C981FAN_REPRESENTATIVE4_CHECKED) then failwith "C981FAN: a Lean decide check fails";;

(* Lean: representative3_excluded *)
let C981FAN_REPRESENTATIVE3_EXCLUDED = c981br_rep_excluded 3 c981fan_excludes;;
(* Lean: representative4_excluded *)
let C981FAN_REPRESENTATIVE4_EXCLUDED = c981br_rep_excluded 4 c981fan_excludes;;

(* the packing-level forms of the Lean theorems at representative 4 *)
let C981FAN_ESCAPING_EXISTS_4 = c981fan_escaping_exists C981FAN_REP4;;
let C981FAN_POSITIVE_BOUNDS_4 = c981fan_positive_bounds_thm C981FAN_REP4;;

(* ========================================================================= *)
(* Port of Compact/Completion/C981/LastRows.lean                              *)
(* (N12Compact.C981CompletionLastRows).  Original representative 29: a      *)
(* genuine ordinary center and the actual wall and corner ancestry enter the *)
(* complete continuous final cycle C981LC_IMPOSSIBLE.  Conventions and       *)
(* helpers of CP_C981_CommonRows.ml (c981cr_apply / _excl / _segment,        *)
(* c981ttr_pull, charts C981CH_*, WallAdvance C981WA_POINT, WallLowerReach   *)
(* WLR_POINT, CornerAdvance C981CA_POINT, WallOrigin C981WO_POINT,           *)
(* Crosspoint C981CP_POINT).  `geometry` is stated for the owners q i with   *)
(* letters 0 S, 1 P, 3 K, 4 E, 5 A, 6 B, 7 C, 8 L, 9 D, 10 R, 11 W, all     *)
(* insidePoints / outsidePoints, the center, and the apart pairs used.       *)
(* `Check v` / `excludes v checked` are the producer c981lr_excludes V        *)
(* (points from c981br_in / c981br_out, center c981dwe_center V 2).          *)
(* Tag C981LR_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_LastCycle.ml";;
needs "n12/geometry/CP_C981_CommonRows.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_C981_WallOrigin.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/CP_C981_Charts.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/C981DoubleWallElbows.ml";;
needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;

(* Lean: insidePoints *)
let c981lr_inside =
  [0, [(`&187 / &100`, `&19 / &25`)];
   1, [(`&19 / &25`, `&187 / &100`); (`&1`, `&87 / &50`)];
   3, [(`&3`, `&3`)];
   4, [(`&1`, `&3`)];
   5, [(`&47 / &20`, `&33 / &20`); (`&2`, `&87 / &50`); (`&113 / &50`, `&2`)];
   6, [(`&47 / &20`, `&47 / &20`); (`&113 / &50`, `&3`); (`&12 / &5`, `&3`)];
   7, [(`&33 / &20`, `&47 / &20`); (`&2`, `&113 / &50`); (`&87 / &50`, `&2`)];
   8, [(`&457 / &500`, `&2`); (`&1`, `&113 / &50`); (`&1`, `&12 / &5`)];
   9, [(`&2`, `&457 / &500`); (`&113 / &50`, `&1`); (`&12 / &5`, `&1`)];
   10, [(`&1543 / &500`, `&2`); (`&3`, `&12 / &5`); (`&3`, `&87 / &50`)];
   11, [(`&2`, `&1543 / &500`); (`&8 / &5`, `&3`); (`&87 / &50`, `&3`)]];;

(* Lean: outsidePoints *)
let c981lr_outside =
  [7, [(`&33 / &20`, `&33 / &20`)];
   8, [(`&1`, `&87 / &50`)];
   9, [(`&87 / &50`, `&1`)];
   10, [(`&3`, `&8 / &5`)]];;

let C981LR_LETTERS =
  [0, "S"; 1, "P"; 3, "K"; 4, "E"; 5, "A"; 6, "B"; 7, "C"; 8, "L"; 9, "D"; 10, "R"; 11, "W"];;
let c981lr_q i = c981cr_sq (assoc i C981LR_LETTERS);;
let C981LR_OWNERS = map fst C981LR_LETTERS;;

(* apart pairs (q indices) used by the proof *)
let C981LR_APART =
  [8, 1; 8, 7; 11, 6; 11, 7; 4, 8; 4, 11; 7, 6; 7, 11; 9, 0; 9, 5;
   6, 10; 6, 3; 5, 10; 5, 9; 7, 1; 7, 5];;

let c981lr_geometry_stmt =
  let qs = map c981lr_q C981LR_OWNERS in
  let unit q = let c = el 0 q and s = el 1 q in mk_eq(mk_binop `(+):real->real->real`
       (mk_binop `( * ):real->real->real` c c) (mk_binop `( * ):real->real->real` s s), `&1`) in
  let side q = mk_binop `(<):real->real->bool` `&1` (el 4 q) in
  let a i = el 4 (c981lr_q i) in
  let same i j = mk_eq(a i, a j) in
  let cap = mk_binop `(<=):real->real->bool` (a 7) `&1001 / &1000` in
  let box q = list_mk_comb(`lcont`, q) in
  let pts = List.concat (map (fun (i, ps) -> map (c981cr_lin (c981lr_q i)) ps) c981lr_inside) in
  let opts = List.concat (map (fun (i, ps) ->
               map (fun p -> mk_neg(c981cr_lin (c981lr_q i) p)) ps) c981lr_outside) in
  let center = c981cr_lin (c981lr_q 7) (`&2`, `&2`) in
  let aps = map (fun (i, j) -> list_mk_comb(`ldisj`, c981lr_q i @ c981lr_q j)) C981LR_APART in
  let body = list_mk_conj(map unit qs @ map side qs @
               [cap; same 7 6; same 7 5; same 6 10] @ map box qs @ pts @ opts @ [center] @ aps) in
  list_mk_forall(List.concat qs, mk_imp(body, `false`));;

(* Lean: geometry *)
let C981LR_GEOMETRY = prove
 (c981lr_geometry_stmt,
  REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    let hs = CONJUNCTS h in
    let get t = try find (fun th -> concl th = t) hs
                with Failure _ -> failwith ("get: " ^ string_of_term t) in
    let q = c981lr_q in
    let s0 = q 0 and p = q 1 and k = q 3 and e = q 4 and a = q 5 and b = q 6
    and c = q 7 and l = q 8 and d = q 9 and r = q 10 and w = q 11 in
    let dj x y = try get (list_mk_comb(`ldisj`, x @ y))
                 with Failure _ -> get (list_mk_comb(`ldisj`, y @ x))
    and pt q pp = get (c981cr_lin q pp) in
    let pos q = MATCH_MP (REAL_ARITH `&1 < x ==> &0 < x`) (get (mk_comb(`(<) (&1)`, el 4 q))) in
    let box q = get (list_mk_comb(`lcont`, q)) in
    let scal = filter (fun th -> is_eq (concl th) || is_real_rel (concl th)) hs in
    let scal = scal @ map (fun i -> pos (q i)) C981LR_OWNERS in
    let ap lemma tuple facts = c981cr_apply lemma tuple (facts @ hs @ scal) scal in
    let lin_mid q th1 th2 (x, y) =
      let tm = c981cr_lin q (x, y) in
      let ths = map (REWRITE_RULE[linside]) [th1; th2] in
      EQ_MP (SYM (REWRITE_CONV[linside] tm))
        (MP (MP (REAL_ARITH (mk_imp(concl(el 0 ths), mk_imp(concl(el 1 ths),
                  rand(concl(REWRITE_CONV[linside] tm)))))) (el 0 ths)) (el 1 ths)) in
    let seg_excl dth sg var lo hi =
      let lot = mk_binop `(<=):real->real->bool` lo var
      and hit = mk_binop `(<=):real->real->bool` var hi in
      let sp = MP (MP (SPEC var sg) (ASSUME lot)) (ASSUME hit) in
      GEN var (DISCH lot (DISCH hit (c981cr_excl dth sp))) in
    (* leftFar, leftSegment *)
    let leftFar = ap C981WA_POINT l
      [c981cr_excl (dj l p) (pt p (`&19 / &25`, `&187 / &100`));
       c981cr_excl (dj l c) (pt c (`&33 / &20`, `&47 / &20`))] in
    let leftSeg = c981cr_segment l (pt l (`&1`, `&113 / &50`)) leftFar `y:real`
                    `&113 / &50` `&14 / &5` `(y - &113 / &50) * &50 / &27` (`&1`, `y:real`) in
    (* topFar via the transform <true,true,true> of W *)
    let wt = c981ttr_pull (true, true, true) w in
    let wtbox = MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (MATCH_MP LCONT_PULLX (box w))) in
    let topFar = ap WLR_POINT wt
      [wtbox; c981cr_excl (dj w b) (pt b (`&113 / &50`, `&3`));
       c981cr_excl (dj w c) (pt c (`&2`, `&113 / &50`))] in
    let topNear = pt w (`&8 / &5`, `&3`) in
    let topMid = lin_mid w topFar topNear (`&3 / &2`, `&3`) in
    (* cornerFar, cornerSegment *)
    let chart q tms = map (vsubst (zip q [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`])) tms in
    let et = chart e [`s:real`; `--c:real`; `u - c - &3 * s`; `v + s - &3 * c`; `a:real`] in
    let cornerFar = ap C981CA_POINT et
      [MATCH_MP C981CH_CORNER_WALL (box e);
       c981cr_excl (dj e l) leftFar;
       c981cr_excl (dj e w) (pt w (`&87 / &50`, `&3`))] in
    let cornerSeg = c981cr_segment e (pt e (`&1`, `&3`)) cornerFar `z:real`
                      `&0` `&3 / &5` `z * &5 / &3` (`&1`, `&3 + z`) in
    (* topOrigin via the top chart of W *)
    let wtop = chart w [`--c:real`; `s:real`; `u - &2 * c - &3 * s`; `--v - a - &2 * s + &3 * c`; `a:real`] in
    let avoid =
      let zt = `z:real` in
      let lohi = `&0 <= z /\ z <= &3 / &5` in
      let a = ASSUME lohi in
      let sg = MP (MP (SPEC zt cornerSeg) (CONJUNCT1 a)) (CONJUNCT2 a) in
      GEN zt (DISCH lohi (c981cr_excl (dj e w) sg)) in
    let topOrigin = ap C981WO_POINT wtop
      [MATCH_MP C981CH_TOP_WALL (box w); avoid] in
    (* north via pullX C *)
    let cx = c981ttr_pull (false, true, false) c in
    let north = ap C981CP_POINT cx
      [c981cr_excl (dj c b) (pt b (`&47 / &20`, `&47 / &20`));
       c981cr_excl (dj l c) (pt l (`&1`, `&12 / &5`));
       c981cr_excl (dj l c) (MP (MP (SPEC `&5 / &2` leftSeg)
          (REAL_ARITH `&113 / &50 <= &5 / &2`)) (REAL_ARITH `&5 / &2 <= &14 / &5`))] in
    (* west via the transform <true,true,false> of C *)
    let ct = c981ttr_pull (true, true, false) c in
    let west = ap C981CP_POINT ct
      [c981cr_excl (dj c b) (pt b (`&47 / &20`, `&47 / &20`));
       c981cr_excl (dj w c) topNear;
       c981cr_excl (dj w c) topMid] in
    (* bottomFar via pullSwap D, bottomSegment *)
    let dsw = c981ttr_pull (true, false, false) d in
    let bottomFar = ap C981WA_POINT dsw
      [MATCH_MP LCONT_PULLSW (box d);
       c981cr_excl (dj d s0) (pt s0 (`&187 / &100`, `&19 / &25`));
       c981cr_excl (dj d a) (pt a (`&47 / &20`, `&33 / &20`))] in
    let bottomSeg = c981cr_segment d (pt d (`&113 / &50`, `&1`)) bottomFar `x:real`
                      `&113 / &50` `&14 / &5` `(x - &113 / &50) * &50 / &27` (`x:real`, `&1`) in
    let topSeg = c981cr_segment w topFar topOrigin `x:real`
                   `&36 / &25` `&2` `(x - &36 / &25) * &25 / &14` (`x:real`, `&3`) in
    let center = pt c (`&2`, `&2`) in
    let cCut = lin_mid c center north (`&2`, `&12 / &5`) in
    let rwall =
      let th = REWRITE_RULE[lcont] (box r) in
      let th1 = SPECL [`x:real`; `y:real`] th in
      GENL [`x:real`; `y:real`]
        (DISCH (lhand (concl th1)) (CONJUNCT1 (CONJUNCT2 (UNDISCH th1)))) in
    ACCEPT_TAC (ap C981LC_IMPOSSIBLE (c @ b @ a @ r)
      [rwall; west; north;
       seg_excl (dj l c) leftSeg `y:real` `&113 / &50` `&14 / &5`;
       seg_excl (dj c w) topSeg `x:real` `&36 / &25` `&2`;
       c981cr_excl (dj b c) cCut;
       c981cr_excl (dj b w) topOrigin;
       c981cr_excl (dj b r) (pt r (`&3`, `&12 / &5`));
       c981cr_excl (dj b k) (pt k (`&3`, `&3`));
       c981cr_excl (dj b w) (pt w (`&2`, `&1543 / &500`));
       c981cr_excl (dj a r) (pt r (`&3`, `&87 / &50`));
       seg_excl (dj a d) bottomSeg `x:real` `&113 / &50` `&14 / &5`;
       c981cr_excl (dj c p) (pt p (`&1`, `&87 / &50`))])));;

(* Lean: Check, excludes.  For a literal vector V: all points of insidePoints / *)
(* outsidePoints are checked (c981br_in / c981br_out fail otherwise), the       *)
(* center comes from DoubleWallElbows.center (placement 2).                    *)
let c981lr_excludes vtm =
  let ins = List.concat (map (fun (i, ps) -> map (c981br_in vtm i) ps) c981lr_inside) in
  let outpts = List.concat (map (fun (i, ps) -> map (c981br_out vtm i) ps) c981lr_outside) in
  let aps = map (fun (i, j) -> c981br_apart vtm i j) C981LR_APART in
  let hyp = C981BR_HYP vtm in
  let cap = GENL C981BR_VARS (DISCH hyp (MATCH_MP OO_SIDE_LE (CONJUNCT1 (ASSUME hyp)))) in
  c981br_prove_excl vtm C981LR_GEOMETRY C981LR_OWNERS
    (ins @ outpts @ [c981dwe_center vtm 2; cap] @ aps);;

(* Lean: checked, representative29_excluded *)
let C981LR_REPRESENTATIVE29_EXCLUDED = c981br_rep_excluded 29 c981lr_excludes;;

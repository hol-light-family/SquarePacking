(* ========================================================================= *)
(* Port of Compact/Completion/C981/CommonRows.lean                            *)
(* (N12Compact.C981CompletionCommonRows).  Nine original common-cycle rows.  *)
(* Conventions of CP_C981_ShortWallRows.ml / Bridge_C981Row27.ml:            *)
(* ExcludesVector = c981vd_excludes_vector, representativeVectors =          *)
(* c981vd_representative_vectors; insidePoints / outsidePoints are the OCaml *)
(* lists c981cr_inside / c981cr_outside; `Check v` and `excludes v checked`  *)
(* are the producer c981cr_excludes V (literal V): every point comes from    *)
(* c981br_in / c981br_out (fail exactly when a point is not in               *)
(* queryInsidePoints / queryOutsidePoints), the center from                  *)
(* c981dwe_center V 2 (DoubleWallElbows.center, fails unless                 *)
(* PlacementCheck v 2), disjointness from c981br_apart.                      *)
(* `geometry` is stated for the owners it uses (q i = square with letter:   *)
(* 1 P, 3 K, 4 E, 6 B, 7 C, 8 L, 10 R, 11 W), with only the used inside /    *)
(* outside / apart hypotheses.  Transform.pull is c981ttr_pull (rewritten by *)
(* LINSIDE_PULLX / PULLY / PULLSW, containers by LCONT_PULLX etc.), pullX q is*)
(* (--c, s, u - 4c, --v - a - 4s, a); Charts.corner / top are the tuples of  *)
(* C981CH_INSIDE_CORNER / C981CH_INSIDE_TOP (walls C981CH_CORNER_WALL /      *)
(* C981CH_TOP_WALL).  WallAdvance / WallLowerReach / CornerAdvance /         *)
(* WallOrigin / Crosspoint / CommonCycle are C981WA_POINT / WLR_POINT /      *)
(* C981CA_POINT / C981WO_POINT / C981CP_POINT / C981CC_IMPOSSIBLE;           *)
(* inside_segment is CES_INSIDE_SEGMENT.  Tag C981CR_.                       *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_CommonCycle.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_C981_WallOrigin.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/CP_C981_Charts.ml";;
needs "n12/geometry/WallLowerReach.ml";;
needs "n12/geometry/C981DoubleWallElbows.ml";;
needs "n12/geometry/C981TwoTipRows.ml";;
needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: insidePoints *)
let c981cr_inside =
  [1, [(`&19 / &25`, `&187 / &100`)];
   3, [(`&3`, `&3`)];
   4, [(`&1`, `&3`)];
   6, [(`&47 / &20`, `&47 / &20`); (`&113 / &50`, `&3`); (`&12 / &5`, `&3`)];
   7, [(`&33 / &20`, `&47 / &20`); (`&2`, `&113 / &50`); (`&87 / &50`, `&2`)];
   8, [(`&457 / &500`, `&2`); (`&1`, `&113 / &50`); (`&1`, `&12 / &5`)];
   10, [(`&1543 / &500`, `&2`); (`&3`, `&12 / &5`)];
   11, [(`&2`, `&1543 / &500`); (`&8 / &5`, `&3`); (`&87 / &50`, `&3`)]];;

(* Lean: outsidePoints *)
let c981cr_outside =
  [7, [(`&33 / &20`, `&33 / &20`)];
   8, [(`&1`, `&87 / &50`)];
   10, [(`&3`, `&87 / &50`); (`&113 / &50`, `&2`)]];;

let c981cr_sq n = map (fun p -> mk_var(p ^ n, `:real`)) ["c"; "s"; "u"; "v"; "a"];;
let c981cr_lin q (x, y) = list_mk_comb(`linside`, q @ [x; y]);;

let C981CR_P = c981cr_sq "P" and C981CR_K = c981cr_sq "K" and C981CR_E = c981cr_sq "E"
and C981CR_B = c981cr_sq "B" and C981CR_C = c981cr_sq "C" and C981CR_L = c981cr_sq "L"
and C981CR_R = c981cr_sq "R" and C981CR_W = c981cr_sq "W";;

let c981cr_conv =
  REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW;
               C981CH_INSIDE_CORNER; C981CH_INSIDE_TOP] THENC
  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* ~linside X P from |- ldisj X Y (or ldisj Y X) and |- linside Y P *)
let c981cr_excl dth pth =
  let x = rand (rator (concl pth)) and y = rand (concl pth) in
  let d = SPECL [x; y] (REWRITE_RULE[ldisj] dth) in
  try MP (MATCH_MP (TAUT `~(p /\ q) ==> q ==> ~p`) d) pth
  with Failure _ -> MP (MATCH_MP (TAUT `~(p /\ q) ==> p ==> ~q`) d) pth;;

(* apply a lemma (premises a conjunction) to a tuple, normalising pulls and   *)
(* charts, discharging the premises from facts (exact, normalised, rational  *)
(* evaluation, or REAL_ARITH from one of the scalar facts)                   *)
let c981cr_apply lemma tuple facts scalars =
  let th = CONV_RULE (LAND_CONV c981cr_conv THENC RAND_CONV c981cr_conv) (SPECL tuple lemma) in
  let ant = lhand (concl th) in
  let nfacts = map (CONV_RULE c981cr_conv) facts in
  let rec prv t =
    if t = `true` then TRUTH else
    if is_conj t then CONJ (prv (lhand t)) (prv (rand t)) else
    try find (fun f -> aconv (concl f) t) facts with Failure _ ->
    try find (fun f -> aconv (concl f) t) nfacts with Failure _ ->
    try EQT_ELIM ((ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV THENC REWRITE_CONV[]) t) with Failure _ ->
    try tryfind (fun f -> MP (REAL_ARITH (mk_imp(concl f, t))) f) scalars with Failure _ ->
    failwith ("c981cr_apply: " ^ string_of_term t) in
  MP th (prv ant);;

(* the segment !t. lo <= t ==> t <= hi ==> linside q (x t) (y t) from the    *)
(* end points p0, p1 and the parameter s(t) in [0,1]                          *)
let c981cr_segment q p0 p1 var lo hi par (xg, yg) =
  let (x0, y0) = (rand(rator(concl p0)), rand(concl p0))
  and (x1, y1) = (rand(rator(concl p1)), rand(concl p1)) in
  let lot = mk_binop `(<=):real->real->bool` lo var
  and hit = mk_binop `(<=):real->real->bool` var hi in
  let bnd = REAL_ARITH (mk_imp(lot, mk_imp(hit,
              mk_conj(mk_binop `(<=):real->real->bool` `&0` par,
                      mk_binop `(<=):real->real->bool` par `&1`)))) in
  let b = MP (MP bnd (ASSUME lot)) (ASSUME hit) in
  let th = MP (SPECL (q @ [x0; y0; x1; y1; par]) CES_INSIDE_SEGMENT)
              (CONJ p0 (CONJ p1 b)) in
  let xt = rand(rator(concl th)) and yt = rand(concl th) in
  let th' = CONV_RULE (RAND_CONV (K (REAL_ARITH (mk_eq(yt, yg)))) THENC
                       RATOR_CONV(RAND_CONV (K (REAL_ARITH (mk_eq(xt, xg)))))) th in
  GEN var (DISCH lot (DISCH hit th'));;

(* Lean: geometry *)
let C981CR_GEOMETRY = prove
 (`forall cP sP uP vP aP cK sK uK vK aK cE sE uE vE aE cB sB uB vB aB
    cC sC uC vC aC cL sL uL vL aL cR sR uR vR aR cW sW uW vW aW.
     cE * cE + sE * sE = &1 /\ cB * cB + sB * sB = &1 /\ cC * cC + sC * sC = &1 /\
     cL * cL + sL * sL = &1 /\ cR * cR + sR * sR = &1 /\ cW * cW + sW * sW = &1 /\
     &1 < aE /\ &1 < aB /\ &1 < aC /\ &1 < aL /\ &1 < aR /\ &1 < aW /\ aC = aB /\
     lcont cE sE uE vE aE /\ lcont cL sL uL vL aL /\ lcont cR sR uR vR aR /\
     lcont cW sW uW vW aW /\
     linside cP sP uP vP aP (&19 / &25) (&187 / &100) /\
     linside cK sK uK vK aK (&3) (&3) /\
     linside cE sE uE vE aE (&1) (&3) /\
     linside cB sB uB vB aB (&47 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&113 / &50) (&3) /\
     linside cB sB uB vB aB (&12 / &5) (&3) /\
     linside cC sC uC vC aC (&33 / &20) (&47 / &20) /\
     linside cC sC uC vC aC (&2) (&113 / &50) /\
     linside cC sC uC vC aC (&87 / &50) (&2) /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cL sL uL vL aL (&1) (&113 / &50) /\
     linside cL sL uL vL aL (&1) (&12 / &5) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cW sW uW vW aW (&2) (&1543 / &500) /\
     linside cW sW uW vW aW (&8 / &5) (&3) /\
     linside cW sW uW vW aW (&87 / &50) (&3) /\
     ~linside cC sC uC vC aC (&33 / &20) (&33 / &20) /\
     ~linside cL sL uL vL aL (&1) (&87 / &50) /\
     ~linside cR sR uR vR aR (&3) (&87 / &50) /\
     ~linside cR sR uR vR aR (&113 / &50) (&2) /\
     linside cC sC uC vC aC (&2) (&2) /\
     ldisj cL sL uL vL aL cP sP uP vP aP /\ ldisj cL sL uL vL aL cC sC uC vC aC /\
     ldisj cW sW uW vW aW cB sB uB vB aB /\ ldisj cW sW uW vW aW cC sC uC vC aC /\
     ldisj cE sE uE vE aE cL sL uL vL aL /\ ldisj cE sE uE vE aE cW sW uW vW aW /\
     ldisj cC sC uC vC aC cB sB uB vB aB /\ ldisj cB sB uB vB aB cR sR uR vR aR /\
     ldisj cB sB uB vB aB cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    let hs = CONJUNCTS h in
    let get t = try find (fun th -> concl th = t) hs
                with Failure _ -> failwith ("get: " ^ string_of_term t) in
    let p = C981CR_P and k = C981CR_K and e = C981CR_E and b = C981CR_B
    and c = C981CR_C and l = C981CR_L and r = C981CR_R and w = C981CR_W in
    let dj x y = get (list_mk_comb(`ldisj`, x @ y)) and pt q pp = get (c981cr_lin q pp) in
    let pos q = MATCH_MP (REAL_ARITH `&1 < x ==> &0 < x`) (get (mk_comb(`(<) (&1)`, el 4 q))) in
    let box q = get (list_mk_comb(`lcont`, q)) in
    let scal = filter (fun th -> is_eq (concl th) || is_real_rel (concl th)) hs in
    let scal = scal @ map pos [e; b; c; l; r; w] in
    let ap lemma tuple facts = c981cr_apply lemma tuple (facts @ hs @ scal) scal in
    (* leftFar, leftSegment *)
    let leftFar = ap C981WA_POINT l
      [c981cr_excl (dj l p) (pt p (`&19 / &25`, `&187 / &100`));
       c981cr_excl (dj l c) (pt c (`&33 / &20`, `&47 / &20`))] in
    let leftSeg = c981cr_segment l (pt l (`&1`, `&113 / &50`)) leftFar `y:real`
                    `&113 / &50` `&14 / &5` `(y - &113 / &50) * &50 / &27` (`&1`, `y:real`) in
    (* topFar via the transform <true,true,true> of W *)
    let t3 = (true, true, true) in
    let wt = c981ttr_pull t3 w in
    let wtbox = MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (MATCH_MP LCONT_PULLX (box w))) in
    let topFar = ap WLR_POINT wt
      [wtbox; c981cr_excl (dj w b) (pt b (`&113 / &50`, `&3`));
       c981cr_excl (dj w c) (pt c (`&2`, `&113 / &50`))] in
    let topNear = pt w (`&8 / &5`, `&3`) in
    let lin_mid q th1 th2 (x, y) =
      let tm = c981cr_lin q (x, y) in
      let ths = map (REWRITE_RULE[linside]) [th1; th2] in
      EQ_MP (SYM (REWRITE_CONV[linside] tm))
        (MP (MP (REAL_ARITH (mk_imp(concl(el 0 ths), mk_imp(concl(el 1 ths),
                  rand(concl(REWRITE_CONV[linside] tm)))))) (el 0 ths)) (el 1 ths)) in
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
      let seg = MP (MP (SPEC zt cornerSeg) (CONJUNCT1 a)) (CONJUNCT2 a) in
      GEN zt (DISCH lohi (c981cr_excl (dj e w) seg)) in
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
    (* rightFar via pullX R *)
    let rx = c981ttr_pull (false, true, false) r in
    let rightFar = ap WLR_POINT rx [MATCH_MP LCONT_PULLX (box r)] in
    let rightHigh = pt r (`&3`, `&12 / &5`) in
    let rightMid = lin_mid r rightHigh rightFar (`&3`, `&5 / &2`) in
    let cCut = lin_mid c (pt c (`&2`, `&2`)) north (`&2`, `&12 / &5`) in
    let segC =
      let yt = `y:real` in
      let lo = `&113 / &50 <= y` and hi = `y <= &14 / &5` in
      let s = MP (MP (SPEC yt leftSeg) (ASSUME lo)) (ASSUME hi) in
      GEN yt (DISCH lo (DISCH hi (c981cr_excl (dj l c) s))) in
    ACCEPT_TAC (ap C981CC_IMPOSSIBLE (c @ b)
      [west; north; segC;
       c981cr_excl (dj c b) cCut;
       c981cr_excl (dj w b) topOrigin;
       c981cr_excl (dj b r) rightHigh;
       c981cr_excl (dj b k) (pt k (`&3`, `&3`));
       c981cr_excl (dj b r) rightFar;
       c981cr_excl (dj b r) rightMid;
       c981cr_excl (dj w b) (pt w (`&2`, `&1543 / &500`))])));;

(* Lean: Check, excludes.  For a literal vector V: all points of insidePoints / *)
(* outsidePoints are checked (c981br_in / c981br_out fail otherwise), the       *)
(* center comes from DoubleWallElbows.center (placement 2) and the geometry is  *)
(* applied to the owners 1,3,4,6,7,8,10,11.                                     *)
let c981cr_excludes vtm =
  let ins = List.concat (map (fun (i, ps) -> map (c981br_in vtm i) ps) c981cr_inside) in
  let outs = List.concat (map (fun (i, ps) -> map (c981br_out vtm i) ps) c981cr_outside) in
  let aps = map (fun (i, j) -> c981br_apart vtm i j)
              [8, 1; 8, 7; 11, 6; 11, 7; 4, 8; 4, 11; 7, 6; 6, 10; 6, 3] in
  c981br_prove_excl vtm C981CR_GEOMETRY [1; 3; 4; 6; 7; 8; 10; 11]
    (ins @ outs @ [c981dwe_center vtm 2] @ aps);;

(* Lean: coveredIds *)
let c981cr_covered_ids = new_definition
 `c981cr_covered_ids = [2; 28; 30; 34; 37; 41; 43; 69; 103]`;;

(* Lean: checked *)
let C981CR_CHECKED =
  map (fun i -> c981br_rep_excluded i c981cr_excludes) [2; 28; 30; 34; 37; 41; 43; 69; 103];;

(* Lean: covered_excluded *)
let C981CR_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981cr_covered_ids]
    (c981br_covered [2; 28; 30; 34; 37; 41; 43; 69; 103] C981CR_CHECKED);;

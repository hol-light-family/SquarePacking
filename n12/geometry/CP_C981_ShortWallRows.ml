(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShortWallRows.lean                        *)
(* (N12Compact.C981CompletionShortWallRows).  Original whole-vector          *)
(* exclusions 59, 105, 108.  Their actual top owner reaches (2.73,3) by the  *)
(* origin/tip alternatives; both central owners then strictly contain        *)
(* (2.54,1.99).  ExcludesVector = c981vd_excludes_vector,                    *)
(* representativeVectors = c981vd_representative_vectors (VectorData).       *)
(* insidePoints / outsidePoints are the OCaml lists c981swr_inside /         *)
(* c981swr_outside; `Check v` and `excludes v checked` are the producer      *)
(* c981swr_excludes V (literal V): every point comes from c981br_in /        *)
(* c981br_out (Bridge_C981Row27.ml), which fail exactly when a point is not  *)
(* in queryInsidePoints / queryOutsidePoints; disjointness from c981br_apart.*)
(* The geometric theorems `ending` and `geometry` are stated for the owners  *)
(* they use (q i = square with letter: 1 P, 3 K, 5 A, 6 B, 7 N, 8 L, 9 D,    *)
(* 10 R, 11 W), with only the used inside / outside / apart hypotheses.      *)
(* ShortWallCycle.impossible = C981SWC_IMPOSSIBLE; WallAdvance.point =       *)
(* C981WA_POINT; Charts.shiftedTop / inside_shiftedTop / shiftedTop_wall =   *)
(* C981CH_INSIDE_SHIFTEDTOP / C981CH_SHIFTEDTOP_WALL; TopReach.central_tip / *)
(* foreign_tip / origin_alternative = C981TR_*; inside_segment =             *)
(* CES_INSIDE_SEGMENT.  Tag C981SWR_.                                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_TopReach.ml";;
needs "n12/geometry/CP_C981_ShortWallCycle.ml";;
needs "n12/geometry/CP_C981_Charts.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/VectorData.ml";;
needs "n12/geometry/Bridge_C981Row27.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* Lean: insidePoints *)
let c981swr_inside =
  [1, [(`&19 / &25`, `&187 / &100`)];
   3, [(`&3`, `&3`); (`&1543 / &500`, `&3`)];
   5, [(`&47 / &20`, `&33 / &20`); (`&2`, `&87 / &50`); (`&113 / &50`, `&2`)];
   6, [(`&47 / &20`, `&47 / &20`); (`&3`, `&113 / &50`); (`&3`, `&12 / &5`)];
   7, [(`&33 / &20`, `&47 / &20`); (`&2`, `&113 / &50`); (`&87 / &50`, `&3`)];
   8, [(`&457 / &500`, `&2`); (`&1`, `&113 / &50`); (`&1`, `&12 / &5`)];
   9, [(`&12 / &5`, `&1`)];
   10, [(`&1543 / &500`, `&2`)];
   11, [(`&2`, `&1543 / &500`); (`&12 / &5`, `&3`); (`&113 / &50`, `&3`)]];;

(* Lean: outsidePoints *)
let c981swr_outside =
  [5, [(`&33 / &20`, `&33 / &20`)];
   7, [(`&8 / &5`, `&3`); (`&87 / &50`, `&2`)];
   8, [(`&1`, `&87 / &50`)]];;

let c981swr_sq n = map (fun p -> mk_var(p ^ n, `:real`)) ["c"; "s"; "u"; "v"; "a"];;
let c981swr_lin q (x, y) = list_mk_comb(`linside`, q @ [x; y]);;

(* ~linside X P from |- ldisj X Y and |- linside Y P *)
let c981swr_excl dth pth =
  let x = rand (rator (concl pth)) and y = rand (concl pth) in
  let d = SPECL [x; y] (REWRITE_RULE[ldisj] dth) in
  MP (MATCH_MP (TAUT `~(p /\ q) ==> q ==> ~p`) d) pth;;

(* ~linside Y P from |- ldisj X Y and |- linside X P *)
let c981swr_excl2 dth pth =
  let x = rand (rator (concl pth)) and y = rand (concl pth) in
  let d = SPECL [x; y] (REWRITE_RULE[ldisj] dth) in
  MP (MATCH_MP (TAUT `~(p /\ q) ==> p ==> ~q`) d) pth;;

(* apply lemma (premises a conjunction) to the tuple, normalising the        *)
(* shiftedTop chart when sh is true, discharging the premises from facts     *)
let c981swr_apply lemma tuple sh facts =
  let conv = if sh then REWRITE_CONV[C981CH_INSIDE_SHIFTEDTOP] THENC
                        ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV
             else ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let th = CONV_RULE (LAND_CONV conv THENC RAND_CONV conv) (SPECL tuple lemma) in
  let ant = lhand (concl th) in
  let rec prv t =
    if is_conj t then CONJ (prv (lhand t)) (prv (rand t)) else
    try find (fun f -> aconv (concl f) t) facts with Failure _ ->
    try EQT_ELIM ((ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV THENC REWRITE_CONV[]) t) with Failure _ ->
    try find (fun f -> aconv (concl (CONV_RULE conv f)) t) facts |> CONV_RULE conv with Failure _ ->
    failwith ("c981swr_apply: " ^ string_of_term t) in
  MP th (prv ant);;

(* Lean: topSegment (local) *)
let C981SWR_TOP_SEGMENT = prove
 (`forall cB sB uB vB aB cW sW uW vW aW.
     linside cW sW uW vW aW (&113 / &50) (&3) /\ linside cW sW uW vW aW (&273 / &100) (&3) /\
     ldisj cB sB uB vB aB cW sW uW vW aW
     ==> forall z. &113 / &50 <= z ==> z <= &273 / &100 ==> ~linside cB sB uB vB aB z (&3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  X_GEN_TAC `z:real` THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `&113 / &50`; `&3`; `&273 / &100`; `&3`;
                `(z - &113 / &50) * &100 / &47`] CES_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall P Q. linside cW sW uW vW aW P Q ==> P = z /\ Q = &3
                      ==> linside cW sW uW vW aW z (&3)`
    (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* Lean: ending *)
let C981SWR_ENDING = prove
 (`forall cK sK uK vK aK cA sA uA vA aA cB sB uB vB aB cD sD uD vD aD
    cR sR uR vR aR cW sW uW vW aW.
     cA * cA + sA * sA = &1 /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aA /\ aA = aB /\
     linside cK sK uK vK aK (&3) (&3) /\ linside cK sK uK vK aK (&1543 / &500) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cB sB uB vB aB (&47 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&3) (&113 / &50) /\
     linside cB sB uB vB aB (&3) (&12 / &5) /\
     linside cD sD uD vD aD (&12 / &5) (&1) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cW sW uW vW aW (&113 / &50) (&3) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cW sW uW vW aW (&273 / &100) (&3) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\ ldisj cA sA uA vA aA cD sD uD vD aD /\
     ldisj cB sB uB vB aB cR sR uR vR aR /\ ldisj cB sB uB vB aB cW sW uW vW aW /\
     ldisj cB sB uB vB aB cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    let hs = CONJUNCTS h in
    let get t = find (fun th -> concl th = t) hs in
    let k = c981swr_sq "K" and a = c981swr_sq "A" and b = c981swr_sq "B"
    and d = c981swr_sq "D" and r = c981swr_sq "R" and w = c981swr_sq "W" in
    let dj x y = get (list_mk_comb(`ldisj`, x @ y)) and pt q p = get (c981swr_lin q p) in
    let seg = MP (SPECL (b @ w) C981SWR_TOP_SEGMENT)
                (end_itlist CONJ [pt w (`&113 / &50`, `&3`); pt w (`&273 / &100`, `&3`); dj b w]) in
    let facts = hs @ [seg;
      c981swr_excl (dj a b) (pt b (`&47 / &20`, `&47 / &20`));
      c981swr_excl (dj a d) (pt d (`&12 / &5`, `&1`));
      c981swr_excl (dj b r) (pt r (`&1543 / &500`, `&2`));
      c981swr_excl (dj b w) (pt w (`&113 / &50`, `&3`));
      c981swr_excl (dj b w) (pt w (`&273 / &100`, `&3`));
      c981swr_excl (dj b k) (pt k (`&3`, `&3`));
      c981swr_excl (dj b k) (pt k (`&1543 / &500`, `&3`))] in
    ACCEPT_TAC (c981swr_apply C981SWC_IMPOSSIBLE (a @ b) false facts)));;

(* Lean: geometry *)
let C981SWR_GEOMETRY = prove
 (`forall cP sP uP vP aP cK sK uK vK aK cA sA uA vA aA cB sB uB vB aB
    cN sN uN vN aN cL sL uL vL aL cD sD uD vD aD cR sR uR vR aR cW sW uW vW aW.
     cA * cA + sA * sA = &1 /\ cB * cB + sB * sB = &1 /\ cN * cN + sN * sN = &1 /\
     cL * cL + sL * sL = &1 /\ cW * cW + sW * sW = &1 /\
     &1 < aA /\ &1 < aB /\ &1 < aN /\ &1 < aL /\ &1 < aW /\ aA = aB /\
     lcont cL sL uL vL aL /\ lcont cW sW uW vW aW /\
     linside cP sP uP vP aP (&19 / &25) (&187 / &100) /\
     linside cK sK uK vK aK (&3) (&3) /\ linside cK sK uK vK aK (&1543 / &500) (&3) /\
     linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&2) (&87 / &50) /\
     linside cA sA uA vA aA (&113 / &50) (&2) /\
     linside cB sB uB vB aB (&47 / &20) (&47 / &20) /\
     linside cB sB uB vB aB (&3) (&113 / &50) /\
     linside cB sB uB vB aB (&3) (&12 / &5) /\
     linside cN sN uN vN aN (&33 / &20) (&47 / &20) /\
     linside cN sN uN vN aN (&2) (&113 / &50) /\
     linside cN sN uN vN aN (&87 / &50) (&3) /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cL sL uL vL aL (&1) (&12 / &5) /\
     linside cD sD uD vD aD (&12 / &5) (&1) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cW sW uW vW aW (&2) (&1543 / &500) /\
     linside cW sW uW vW aW (&12 / &5) (&3) /\
     linside cW sW uW vW aW (&113 / &50) (&3) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cN sN uN vN aN (&8 / &5) (&3) /\
     ~linside cN sN uN vN aN (&87 / &50) (&2) /\
     ~linside cL sL uL vL aL (&1) (&87 / &50) /\
     ldisj cL sL uL vL aL cP sP uP vP aP /\ ldisj cL sL uL vL aL cN sN uN vN aN /\
     ldisj cN sN uN vN aN cW sW uW vW aW /\ ldisj cN sN uN vN aN cB sB uB vB aB /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\ ldisj cA sA uA vA aA cD sD uD vD aD /\
     ldisj cB sB uB vB aB cR sR uR vR aR /\ ldisj cB sB uB vB aB cW sW uW vW aW /\
     ldisj cB sB uB vB aB cK sK uK vK aK
     ==> false`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    let hs = CONJUNCTS h in
    let get t = try find (fun th -> concl th = t) hs
                with Failure _ -> failwith ("get: " ^ string_of_term t) in
    let p = c981swr_sq "P" and k = c981swr_sq "K" and a = c981swr_sq "A"
    and b = c981swr_sq "B" and n = c981swr_sq "N" and l = c981swr_sq "L"
    and d = c981swr_sq "D" and r = c981swr_sq "R" and w = c981swr_sq "W" in
    let dj x y = get (list_mk_comb(`ldisj`, x @ y)) and pt q p = get (c981swr_lin q p) in
    let pos q = let th = get (mk_comb(`(<) (&1)`, el 4 q)) in
                MATCH_MP (REAL_ARITH `&1 < x ==> &0 < x`) th in
    let shift q =
      map (vsubst (zip q [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]))
        [`c:real`; `s:real`; `u - &2 * c - &3 * s`; `v + &2 * s - &3 * c`; `a:real`] in
    let wall q = REWRITE_RULE[C981CH_INSIDE_SHIFTEDTOP]
                   (MATCH_MP C981CH_SHIFTEDTOP_WALL (get (list_mk_comb(`lcont`, q)))) in
    let leftFar = c981swr_apply C981WA_POINT l false
      (hs @ [pos l; c981swr_excl (dj l p) (pt p (`&19 / &25`, `&187 / &100`));
                    c981swr_excl (dj l n) (pt n (`&33 / &20`, `&47 / &20`))]) in
    let wfacts = hs @ [pos w; wall w] in
    let origin = c981swr_lin w (`&2`, `&3`) in
    let topFar =
      DISJ_CASES (SPEC origin EXCLUDED_MIDDLE)
       (let ow = ASSUME origin in
        let tip = c981swr_apply C981TR_CENTRAL_TIP (shift n) true
          (hs @ [pos n; c981swr_excl (dj n w) ow;
                 c981swr_excl (dj n b) (pt b (`&47 / &20`, `&47 / &20`));
                 c981swr_excl2 (dj l n) leftFar]) in
        c981swr_apply C981TR_FOREIGN_TIP (shift w) true
          (wfacts @ [c981swr_excl2 (dj n w) tip;
                     c981swr_excl2 (dj n w) (pt n (`&2`, `&113 / &50`))]))
       (let ow = ASSUME (mk_neg origin) in
        let far = c981swr_apply C981TR_ORIGIN_ALTERNATIVE (shift w) true (ow :: wfacts) in
        let near = pt w (`&12 / &5`, `&3`) in
        let tm = c981swr_lin w (`&273 / &100`, `&3`) in
        MP (MP (prove(mk_imp(concl far, mk_imp(concl near, tm)),
                      REWRITE_TAC[linside] THEN REAL_ARITH_TAC)) far) near) in
    ACCEPT_TAC (c981swr_apply C981SWR_ENDING (k @ a @ b @ d @ r @ w) false (topFar :: pos b :: hs))));;

(* Lean: Check, excludes.  For a literal vector V: all points of insidePoints / *)
(* outsidePoints are checked (c981br_in / c981br_out fail otherwise) and the    *)
(* geometry is applied to the owners 1,3,5,6,7,8,9,10,11.                      *)
let c981swr_excludes vtm =
  let ins = List.concat (map (fun (i, ps) -> map (c981br_in vtm i) ps) c981swr_inside) in
  let c981swr_outs = List.concat (map (fun (i, ps) -> map (c981br_out vtm i) ps) c981swr_outside) in
  let aps = map (fun (i, j) -> c981br_apart vtm i j)
              [8, 1; 8, 7; 7, 11; 7, 6; 5, 6; 5, 9; 6, 10; 6, 11; 6, 3] in
  c981br_prove_excl vtm C981SWR_GEOMETRY [1; 3; 5; 6; 7; 8; 9; 10; 11] (ins @ c981swr_outs @ aps);;

(* Lean: coveredIds *)
let c981swr_covered_ids = new_definition
 `c981swr_covered_ids = [59; 105; 108]`;;

(* Lean: checked *)
let C981SWR_CHECKED = map (fun i -> c981br_rep_excluded i c981swr_excludes) [59; 105; 108];;

(* Lean: covered_excluded *)
let C981SWR_COVERED_EXCLUDED =
  REWRITE_RULE[GSYM c981swr_covered_ids] (c981br_covered [59; 105; 108] C981SWR_CHECKED);;

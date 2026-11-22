(* ========================================================================= *)
(* Port of Compact/Completion/C981/ShortWall71.lean                          *)
(* (N12Compact.C981CompletionShortWall71).  Original representative 71.  Its *)
(* northwest central square really owns (1.6,3), so this entrance uses the  *)
(* full actual left-wall segment and the circular cap instead of the        *)
(* isolated omission used in the other rows.  Conventions as in             *)
(* CP_C981_ShortWallRows.ml (squares 1 P, 3 K, 5 A, 6 B, 7 N, 8 L, 9 D,     *)
(* 10 R, 11 W).  Lean `excludes` is the producer c981sw71_excludes V; its    *)
(* geometric content is C981SW71_GEOMETRY (only the used hypotheses).        *)
(* canonical_frame = CLF_CANONICAL_FRAME; ShallowCap.positive_tip /          *)
(* negative_cap / Cap = C981SC_POSITIVE_TIP / C981SC_NEGATIVE_CAP /          *)
(* c981sc_cap; ShallowWall.point = C981SW_POINT.  Tag C981SW71_.             *)
(* ========================================================================= *)

needs "n12/geometry/CP_C981_ShortWallRows.ml";;
needs "n12/geometry/CP_C981_ShallowWall.ml";;

(* Lean: outsidePoints *)
let c981sw71_outside =
  [5, [(`&33 / &20`, `&33 / &20`)];
   7, [(`&87 / &50`, `&2`)];
   8, [(`&1`, `&87 / &50`)]];;

(* Lean: leftSegment + nSegment (local): the actual left wall segment of L   *)
(* excludes N from x = 1, 113/50 <= 3 + y <= 14/5                           *)
let C981SW71_SEGMENT_AVOID = prove
 (`forall cN sN uN vN aN cL sL uL vL aL.
     linside cL sL uL vL aL (&1) (&113 / &50) /\ linside cL sL uL vL aL (&1) (&14 / &5) /\
     ldisj cL sL uL vL aL cN sN uN vN aN
     ==> forall y. --(&37 / &50) <= y /\ y <= --(&1 / &5) ==> ~linside cN sN uN vN aN (&1) (&3 + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real` THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                `&1`; `&113 / &50`; `&1`; `&14 / &5`;
                `((&3 + y) - &113 / &50) * &50 / &27`] CES_INSIDE_SEGMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `forall P Q. linside cL sL uL vL aL P Q ==> P = &1 /\ Q = &3 + y
                      ==> linside cL sL uL vL aL (&1) (&3 + y)`
    (fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* the canonical-frame split of the shifted northwest square n (Lean: the    *)
(* by_cases on r.s inside topFar): either the tip or the whole cap           *)
let C981SW71_TIP_OR_CAP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (--(&13 / &50)) (&0) /\
     linside c s u v a (&0) (--(&37 / &50)) /\
     ~linside c s u v a (&0) (&0) /\
     ~linside c s u v a (--(&13 / &50)) (--(&1)) /\
     (forall y. --(&37 / &50) <= y /\ y <= --(&1 / &5) ==> ~linside c s u v a (--(&1)) y)
     ==> linside c s u v a (--(&3 / &100)) (&0) \/
         (forall x y. c981sc_cap x y ==> linside c s u v a x y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = a`)) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> can (find_term ((=) `lclosed`)) (concl th))) THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC) THEN
  ASM_CASES_TAC `&0 <= s'` THENL
   [DISJ1_TAC THEN MATCH_MP_TAC C981SC_POSITIVE_TIP THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs s' <= c'` THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN MATCH_MP_TAC C981SC_NEGATIVE_CAP THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `abs s' <= c'` THEN ASM_REAL_ARITH_TAC]);;

(* Lean: avoid (local) *)
let C981SW71_AVOID = prove
 (`forall cN sN uN vN aN cW sW uW vW aW.
     (forall x y. c981sc_cap x y ==> linside cN sN uN vN aN (&2 + x) (&3 + y)) /\
     ldisj cN sN uN vN aN cW sW uW vW aW
     ==> forall x y. c981sc_cap x y ==> ~linside cW sW uW vW aW (&2 + x) (&3 + y)`,
  REWRITE_TAC[ldisj] THEN MESON_TAC[]);;

(* geometric content of Lean `excludes` (representative 71) *)
let C981SW71_GEOMETRY = prove
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
     linside cL sL uL vL aL (&1) (&113 / &50) /\
     linside cL sL uL vL aL (&1) (&12 / &5) /\
     linside cD sD uD vD aD (&12 / &5) (&1) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\
     linside cW sW uW vW aW (&2) (&1543 / &500) /\
     linside cW sW uW vW aW (&12 / &5) (&3) /\
     linside cW sW uW vW aW (&113 / &50) (&3) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cN sN uN vN aN (&87 / &50) (&2) /\
     ~linside cL sL uL vL aL (&1) (&87 / &50) /\
     ldisj cL sL uL vL aL cP sP uP vP aP /\ ldisj cL sL uL vL aL cN sN uN vN aN /\
     ldisj cN sN uN vN aN cW sW uW vW aW /\
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
    let pos q = MATCH_MP (REAL_ARITH `&1 < x ==> &0 < x`) (get (mk_comb(`(<) (&1)`, el 4 q))) in
    let shift q =
      map (vsubst (zip q [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]))
        [`c:real`; `s:real`; `u - &2 * c - &3 * s`; `v + &2 * s - &3 * c`; `a:real`] in
    let wall q = REWRITE_RULE[C981CH_INSIDE_SHIFTEDTOP]
                   (MATCH_MP C981CH_SHIFTEDTOP_WALL (get (list_mk_comb(`lcont`, q)))) in
    let leftFar = c981swr_apply C981WA_POINT l false
      (hs @ [pos l; c981swr_excl (dj l p) (pt p (`&19 / &25`, `&187 / &100`));
                    c981swr_excl (dj l n) (pt n (`&33 / &20`, `&47 / &20`))]) in
    let nSegment = MP (SPECL (n @ l) C981SW71_SEGMENT_AVOID)
      (end_itlist CONJ [pt l (`&1`, `&113 / &50`); leftFar; dj l n]) in
    let wfacts = hs @ [pos w; wall w] in
    let origin = c981swr_lin w (`&2`, `&3`) in
    let topFar =
      DISJ_CASES (SPEC origin EXCLUDED_MIDDLE)
       (let ow = ASSUME origin in
        let split = c981swr_apply C981SW71_TIP_OR_CAP (shift n) true
          (hs @ [pos n; nSegment; c981swr_excl (dj n w) ow]) in
        let tipcase =
          let tip = ASSUME (lhand (concl split)) in
          c981swr_apply C981TR_FOREIGN_TIP (shift w) true
            (wfacts @ [c981swr_excl2 (dj n w) tip;
                       c981swr_excl2 (dj n w) (pt n (`&2`, `&113 / &50`))]) in
        let capcase =
          let cap = ASSUME (rand (concl split)) in
          let avoid = MP (SPECL (n @ w) C981SW71_AVOID) (CONJ cap (dj n w)) in
          c981swr_apply C981SW_POINT (shift w) true (avoid :: wfacts) in
        DISJ_CASES split tipcase capcase)
       (let ow = ASSUME (mk_neg origin) in
        let far = c981swr_apply C981TR_ORIGIN_ALTERNATIVE (shift w) true (ow :: wfacts) in
        let near = pt w (`&12 / &5`, `&3`) in
        let tm = c981swr_lin w (`&273 / &100`, `&3`) in
        MP (MP (prove(mk_imp(concl far, mk_imp(concl near, tm)),
                      REWRITE_TAC[linside] THEN REAL_ARITH_TAC)) far) near) in
    ACCEPT_TAC (c981swr_apply C981SWR_ENDING (k @ a @ b @ d @ r @ w) false
                  (topFar :: pos b :: hs))));;

(* Lean: Check, excludes.  For a literal vector V: all points of             *)
(* ShortWallRows.insidePoints and of outsidePoints are checked              *)
(* (c981br_in / c981br_out fail otherwise).                                  *)
let c981sw71_excludes vtm =
  let ins = List.concat (map (fun (i, ps) -> map (c981br_in vtm i) ps) c981swr_inside) in
  let c981sw71_outs = List.concat (map (fun (i, ps) -> map (c981br_out vtm i) ps) c981sw71_outside) in
  let aps = map (fun (i, j) -> c981br_apart vtm i j)
              [8, 1; 8, 7; 7, 11; 5, 6; 5, 9; 6, 10; 6, 11; 6, 3] in
  c981br_prove_excl vtm C981SW71_GEOMETRY [1; 3; 5; 6; 7; 8; 9; 10; 11]
    (ins @ c981sw71_outs @ aps);;

(* Lean: checked, representative71_excluded *)
let C981SW71_REPRESENTATIVE71_EXCLUDED = c981br_rep_excluded 71 c981sw71_excludes;;

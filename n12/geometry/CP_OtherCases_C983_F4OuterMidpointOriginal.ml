(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4OuterMidpointOriginal.lean.  *)
(* Original-owner adapter for the outer-midpoint support argument, and the  *)
(* paired southeast corner / bottom-wall transfer.  Conventions of           *)
(* CP_OtherCases_C983_F4Filters.ml / F4BottomMidpointOriginal.ml: owners     *)
(* p 1 / 2 / 5 / 7 / 8 / 9 = owner 2 / 12 / 512 / 2304 / 4096 / 8192,        *)
(* actual p i = c983e_actual c1 c2 a b l i; E = cE sE uE vE aE (an           *)
(* OpenSquare: unit normal, 0 < side); (owners p 7).translated 2 2 is the    *)
(* tuple of C983AOP_TRANSLATE.  F4OuterMidpoint.Input = c983f4om_input,      *)
(* F4OuterMidpoint.inside = C983F4OM_INSIDE, point_exact =                   *)
(* C983F4F_POINT_EXACT, left_aux / bottom_aux = C983AB_*, pullX by           *)
(* LINSIDE_PULLX / LCONT_PULLX, WallProfile.boundary_origin =                *)
(* OCWPBO_BOUNDARY_ORIGIN.  Tag C983F4OMO_.                                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_F4CentralFinal.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4OuterMidpoint.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;
needs "n12/geometry/CP_OtherCases_C983_ActualOutwardPair.ml";;

let C983F4OMO_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;

let c983f4omo_trans m =
  let [c; s; u; v; a] = c983ab_own m in
  let sub x y = mk_binop `(-):real->real->real` x y and add x y = mk_binop `(+):real->real->real` x y
  and mul x y = mk_binop `( * ):real->real->real` x y and neg x = mk_comb(`(--):real->real`, x) in
  [c; s; sub u (add (mul c `&2`) (mul s `&2`)); sub v (add (mul (neg s) `&2`) (mul c `&2`)); a];;

(* Lean: labels (local to f4_outer_midpoint_of_frame) *)
let C983F4OMO_CORNER_LABELS = prove
 (`forall s. MEM s (EL 1 c983e_original_components) ==> 10 IN s`, c983f4f_check_tac);;

(* Lean: f4_outer_midpoint_of_frame *)
let C983F4OMO_F4_OUTER_MIDPOINT_OF_FRAME =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let f4tm = c983f4f_mem 4 7 and nf5tm = mk_neg (c983f4f_mem 5 7) in
  let centertm = c983ab_in 2304 `&2` `&2` in
  let unitE = `cE * cE + sE * sE = &1` and posE = `&0 < aE` and shape = `aE = l:real` in
  let phys = mk_forall(`x:real`, mk_forall(`y:real`,
               mk_eq(list_mk_comb(`linside`, C983F4OMO_E @ [`x:real`; `y:real`]),
                     c983ab_in 512 `x + &2` `y + &2`))) in
  let data = `f4bm_southeast_data cE sE uE vE aE t` in
  let half = `t / (&1 + cE) < &3 / &20` and lowerU = `&13 / &50 * t <= uE` in
  let hyps = [f4tm; nf5tm; centertm; unitE; posE; shape; phys; data; half; lowerU] in
  let stmt = list_mk_forall(C983E_VARS @ C983F4OMO_E @ [`t:real`],
               mk_imp(list_mk_conj ([C983F4F_NP; C983F4F_IMG] @ hyps), c983ab_in 512 `&3` `&3 / &2`)) in
  let f4 = ASSUME f4tm in
  let corner =
    let th = MATCH_MP C983F4OMO_CORNER_LABELS (c983f4f_orig 1) in
    c983f4f_point th in
  let east = c983f5_use C983F4CF_F4_SOUTHEAST_CROSSPOINT [f4] in
  let leftAux = c983f5_use C983AB_LEFT_AUX [] in
  let disj =
    let tm = list_mk_comb(`ldisj`, c983f4omo_trans 2304 @ C983F4OMO_E) in
    let d = REWRITE_RULE[ldisj] (MP (SPECL C983E_VARS (oo_apart C983E_F 2304 512)) (c983f4f_hh ())) in
    EQ_MP (SYM (REWRITE_CONV[ldisj; C983AOP_TRANSLATE; ASSUME phys] tm))
          (GEN `x:real` (GEN `y:real` (SPECL [`x + &2`; `y + &2`] d))) in
  let conv = REWRITE_CONV[C983AOP_TRANSLATE; ASSUME phys] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let facts = [ASSUME data; SYM (ASSUME shape); ASSUME half; ASSUME lowerU; east;
               seed 7 `&33 / &20` `&33 / &20`; seed 7 `&33 / &20` `&47 / &20`; c983f4f_point f4;
               ASSUME centertm; PROVE_HYP (ASSUME nf5tm) (c983sa_missing 5 7);
               excl 2304 4096 (CONJUNCT1 leftAux); excl 2304 2 corner; disj] in
  let input = c983sa_apply conv
    (SPECL (c983f4omo_trans 2304 @ C983F4OMO_E @ [`t:real`])
       (prove(`forall cW sW uW vW aW cE sE uE vE aE t.
                 (f4bm_southeast_data cE sE uE vE aE t /\ aW = aE /\ t / (&1 + cE) < &3 / &20 /\
                  &13 / &50 * t <= uE /\
                  linside cE sE uE vE aE (&1 / &2) (&0) /\
                  linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
                  linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
                  linside cW sW uW vW aW (&0) (--(&13 / &50)) /\
                  linside cW sW uW vW aW (&0) (&0) /\
                  ~linside cW sW uW vW aW (&0) (&13 / &50) /\
                  ~linside cW sW uW vW aW (--(&1)) (&13 / &50) /\
                  ~linside cW sW uW vW aW (--(&1)) (--(&2 / &5)) /\
                  ldisj cW sW uW vW aW cE sE uE vE aE)
                 ==> c983f4om_input cW sW uW vW aW cE sE uE vE aE t`,
              REWRITE_TAC[c983f4om_input]))) facts in
  let th = MP (SPECL (c983f4omo_trans 2304 @ C983F4OMO_E @ [`t:real`]) C983F4OM_INSIDE)
              (end_itlist CONJ [unit 2304; pos; ASSUME unitE; ASSUME posE; input]) in
  let th = CONV_RULE conv th in
  c983f4f_close stmt th;;

let C983F4OMO_PX_BOX_B = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside (--c) s (u - &4 * c) (--v - a - &4 * s) a x y ==> &0 <= y`,
  REWRITE_TAC[lcont; LINSIDE_PULLX] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN REAL_ARITH_TAC);;

let C983F4OMO_PX_BOX_K = prove
 (`forall c s u v a. lcont c s u v a ==> forall x y. linside (--c) s (u - &4 * c) (--v - a - &4 * s) a x y ==> &0 <= x /\ &0 <= y`,
  REWRITE_TAC[lcont; LINSIDE_PULLX] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th)) THEN REAL_ARITH_TAC);;

(* Lean: bottom_origin_of_southeast_outer *)
let C983F4OMO_BOTTOM_ORIGIN_OF_SOUTHEAST_OUTER =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let outertm = c983ab_in 512 `&3` `&3 / &2` in
  let pB = c983fo_pull LINSIDE_PULLX 8192 and pK = c983fo_pull LINSIDE_PULLX 12 in
  let disj =
    let tm = list_mk_comb(`ldisj`, pK @ pB) in
    EQ_MP (SYM (REWRITE_CONV[ldisj; LINSIDE_PULLX] tm))
          (GEN `x:real` (GEN `y:real` (SPECL [`&4 - x`; `y:real`] (apart 12 8192)))) in
  let facts = [unit 8192; unit 12; pos; side; REFL `l:real`;
               MATCH_MP C983F4OMO_PX_BOX_B (box 8192); MATCH_MP C983F4OMO_PX_BOX_K (box 12);
               seed 9 `&2` `&457 / &500`; CONJUNCT1 (c983f5_use C983AB_BOTTOM_AUX []);
               seed 2 `&3` `&457 / &500`; seed 2 `&3` `&1`; excl 12 512 (ASSUME outertm); disj] in
  let th = c983fo_apply (SPECL (pB @ pK @ [`&457 / &500`; `&8 / &5`]) OCWPBO_BOUNDARY_ORIGIN) facts in
  c983f4f_close (c983sa_stmt [outertm] (c983ab_in 8192 `&2` `&1`)) th;;

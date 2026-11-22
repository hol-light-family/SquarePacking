(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C974/LeftOrigin.lean                *)
(* (namespace N12Compact.Completion.OtherCases.C974.OriginalData).  The left *)
(* origin and top halfpoint argument of C974-LEFT-ORIGIN-AND-MIDPOINT.       *)
(* owners p i is the owner of the literal mask EL i c974od_masks (owners 8 = *)
(* 4096, owners 11 = 32768, owners 4 = 192, owners 1 = 2, owners 7 = 1024).  *)
(* fixed = C974EG_FIXED (c974eg_fixed / c974e_compulsory fields), foreign =  *)
(* oo_excl, apart = oo_apart, seed = oo_seed, singleton_vertical =           *)
(* C974OD_SINGLETON_VERTICAL, missing_northwest = oo_missing m 11, top_pair /*)
(* northeast_g7 = C974EG_*.  C981CompletionWallAdvance.point = C981WA_POINT, *)
(* WallUpperMissingReach.point = WUMR_POINT, WallProfile.boundary_origin =   *)
(* OCWPBO_BOUNDARY_ORIGIN, horizontal_segment = OO_HORIZONTAL_SEGMENT.       *)
(* pullX / pullY / pullSwap tuples are those of LCONT_PULLX / Y / SW.        *)
(* Tag C974LO_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C974_EarlyGeometry.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

let C974LO_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C974LO_F = `c974d_family`;;
let c974lo_hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, C974LO_F));;
let c974lo_np = CONJUNCT1 (ASSUME c974lo_hyp);;
let c974lo_gen th = GENL C974LO_VARS (DISCH c974lo_hyp th);;
let c974lo_inst uth = MP (SPECL C974LO_VARS uth) (ASSUME c974lo_hyp);;
let c974lo_tuple m =
  map (fun f -> list_mk_comb(f, C974LO_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c974lo_own m x y = list_mk_comb(`linside`, c974lo_tuple m @ [x; y]);;
let c974lo_stmt body = list_mk_forall(C974LO_VARS, mk_imp(c974lo_hyp, body));;
let c974lo_prove body th = prove(c974lo_stmt body, REPEAT GEN_TAC THEN DISCH_TAC THEN ACCEPT_TAC th);;

(* the fields of Fixed, as theorems under the hypothesis *)
let C974LO_FIXED =
  CONJUNCTS (REWRITE_RULE[c974eg_fixed; c974e_compulsory] (c974lo_inst C974EG_FIXED));;
let c974lo_fixed m x y =
  let tm = c974lo_own m x y in
  try find (fun th -> concl th = tm) C974LO_FIXED with Failure _ -> failwith "c974lo_fixed";;
let c974lo_seed m p = c974lo_inst (oo_inst C974LO_F (oo_seed m p));;
let c974lo_missing m = c974lo_inst (oo_inst C974LO_F (oo_missing m 11));;
let c974lo_excl m n thn = c974lo_inst (oo_excl C974LO_F m n (c974lo_gen thn));;
let c974lo_apart m n = c974lo_inst (oo_apart C974LO_F m n);;
let c974lo_box m = MP (SPECL (C974LO_VARS @ [mk_small_numeral m]) OO_BOX) c974lo_np;;
let c974lo_unit m = MP (SPECL (C974LO_VARS @ [mk_small_numeral m]) OO_UNIT) c974lo_np;;
let C974LO_SIDE = MP (SPECL C974LO_VARS OO_SIDE) c974lo_np;;

let C974LO_PULL_CONV =
  REWRITE_CONV[ldisj; LINSIDE_PULLSW; LINSIDE_PULLY; LINSIDE_PULLX] THENC
  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* a lemma at the tuples of the given (pulled) boxes; antecedent discharged from the facts *)
let c974lo_apply lemma boxes extra ms ths aparts =
  let tuples = List.concat (map (fun b -> snd (strip_comb (concl b))) boxes) in
  let th = CONV_RULE C974LO_PULL_CONV (SPECL (tuples @ extra) lemma) in
  let units = map c974lo_unit ms and obox = map c974lo_box ms in
  let wall = REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(fun h -> let args = snd (strip_comb (concl h)) in
      FIRST (map (fun b g -> MP_TAC (MP (SPECL [el 5 args; el 6 args] (REWRITE_RULE[lcont] b)) h) g) obox)) THEN
    REAL_ARITH_TAC in
  let disj = REPEAT GEN_TAC THEN
    FIRST (map (fun ap -> MATCH_ACCEPT_TAC (REWRITE_RULE[ldisj] ap)) aparts) in
  let close = FIRST [FIRST (map ACCEPT_TAC (ths @ boxes)); ACCEPT_TAC TRUTH; REFL_TAC;
                     MAP_EVERY MP_TAC units THEN REAL_ARITH_TAC;
                     MP_TAC C974LO_SIDE THEN REAL_ARITH_TAC; wall; disj] in
  MP th (TAC_PROOF(([], lhand (concl th)), REPEAT CONJ_TAC THEN close));;

(* Lean: left_reach *)
let C974LO_LEFT_REACH =
  let short = MP (SPECL (C974LO_VARS @ [`&87 / &50`]) C974OD_SINGLETON_VERTICAL)
                 (CONJ c974lo_np (CONJ (CONJUNCT2 (ASSUME c974lo_hyp))
                   (EQT_ELIM (REAL_RAT_REDUCE_CONV `&28 / &25 <= &87 / &50 /\ &87 / &50 <= &87 / &50`)))) in
  let th = c974lo_apply C981WA_POINT [c974lo_box 4096] [] [4096]
    [c974lo_fixed 4096 `&457 / &500` `&2`; c974lo_fixed 4096 `&1` `&12 / &5`;
     c974lo_excl 4096 2 short; c974lo_excl 4096 2 (c974lo_fixed 2 `&19 / &25` `&187 / &100`);
     c974lo_missing 4096] [] in
  c974lo_prove (c974lo_own 4096 `&1` `&14 / &5`) th;;

(* Lean: top_left_reach *)
let C974LO_TOP_LEFT_REACH =
  let boxQ = MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (MATCH_MP LCONT_PULLX (c974lo_box 32768))) in
  let th = c974lo_apply WUMR_POINT [boxQ] [] [32768]
    [c974lo_fixed 32768 `&2` `&1543 / &500`;
     CONJUNCT1 (c974lo_inst C974EG_TOP_PAIR);
     c974lo_excl 32768 1024 (c974lo_inst C974EG_NORTHEAST_G7);
     c974lo_missing 32768] [] in
  c974lo_prove (c974lo_own 32768 `&36 / &25` `&3`) th;;

(* Lean: top_halfpoint *)
let C974LO_TOP_HALFPOINT =
  let th = MP (SPECL (c974lo_tuple 32768 @ [`&36 / &25`; `&8 / &5`; `&3`; `&3 / &2`]) OO_HORIZONTAL_SEGMENT)
    (end_itlist CONJ [c974lo_inst C974LO_TOP_LEFT_REACH; CONJUNCT1 (c974lo_inst C974EG_TOP_PAIR);
                      EQT_ELIM (REAL_RAT_REDUCE_CONV `&36 / &25 < &8 / &5`);
                      EQT_ELIM (REAL_RAT_REDUCE_CONV `&36 / &25 <= &3 / &2`);
                      EQT_ELIM (REAL_RAT_REDUCE_CONV `&3 / &2 <= &8 / &5`)]) in
  c974lo_prove (c974lo_own 32768 `&3 / &2` `&3`) th;;

(* Lean: left_origin *)
let C974LO_LEFT_ORIGIN =
  let pullsy m = MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLY (c974lo_box m)) in
  let th = c974lo_apply OCWPBO_BOUNDARY_ORIGIN [pullsy 4096; pullsy 192] [`&457 / &500`; `&8 / &5`] [4096; 192]
    [c974lo_fixed 4096 `&457 / &500` `&2`; c974lo_fixed 4096 `&1` `&12 / &5`;
     c974lo_seed 192 (`&457 / &500`, `&3`); c974lo_fixed 192 `&1` `&3`;
     c974lo_excl 192 32768 (c974lo_inst C974LO_TOP_HALFPOINT)]
    [c974lo_apart 192 4096] in
  c974lo_prove (c974lo_own 4096 `&1` `&2`) th;;

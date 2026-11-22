(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/F4BottomMidpointOriginal.lean *)
(* Actual-owner adapter for the direct bottom-midpoint exclusion.            *)
(* owners p 0 / 5 / 7 / 9 = owner 1 / 512 / 2304 / 8192 (5-tuples, side l);  *)
(* actual p 7 = c983e_actual c1 c2 a b l 7.  E = cE sE uE vE aE (an          *)
(* OpenSquare: unit normal, 0 < side).  (owners p 9).translated 2 2 is the  *)
(* tuple (c, s, u - 2c - 2s, v + 2s - 2c, l) (C983BMO_TRANSLATED:           *)
(* Inside x y <=> owner (x + 2) (y + 2)).  F4BottomMidpoint.SoutheastData =  *)
(* f4bm_southeast_data, excluded = F4BM_EXCLUDED.  Tag C983BMO_.            *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_ActualBars.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4BottomMidpoint.ml";;

(* Lean: inside_translated_iff (at the shift (2, 2)) *)
let C983BMO_TRANSLATED = prove
 (`forall c s u v a x y. linside c s (u - &2 * c - &2 * s) (v + &2 * s - &2 * c) a x y <=>
                   linside c s u v a (x + &2) (y + &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* prove  !vars. A1 /\ .. /\ An ==> C  from a theorem th whose hypotheses are C983AB_H
   (= A1 /\ A2) or among the Ai *)
let c983bmo_close vars stmt th =
  prove(stmt, REPEAT GEN_TAC THEN DISCH_THEN(fun h ->
    let cs = CONJUNCTS h in
    let fh t = if t = C983AB_H then CONJ (el 0 cs) (el 1 cs)
               else try find (fun c -> concl c = t) cs
                    with Failure _ -> failwith ("c983bmo_close: " ^ string_of_term t) in
    ACCEPT_TAC (itlist (fun t th -> PROVE_HYP (fh t) th) (hyp th) th)));;

let C983BMO_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;

(* Lean: f4_bottom_midpoint_excluded_of_frame *)
let C983BMO_F4_BOTTOM_MIDPOINT_EXCLUDED_OF_FRAME =
  let f4tm = `4 IN c983e_actual c1 c2 a b l 7` in
  let unitE = `cE * cE + sE * sE = &1` and posE = `&0 < aE` and shape = `aE = l:real` in
  let phys = mk_forall(`x:real`, mk_forall(`y:real`,
               mk_eq(list_mk_comb(`linside`, C983BMO_E @ [`x:real`; `y:real`]),
                     c983ab_in 512 `x + &2` `y + &2`))) in
  let data = `f4bm_southeast_data cE sE uE vE aE t` in
  let corner = c983ab_in 1 `&49 / &25` `&19 / &25` in
  let concl0 = mk_neg(c983ab_in 8192 `&2` `&3 / &2`) in
  let stmt = list_mk_forall(C983E_VARS @ C983BMO_E @ [`t:real`],
               mk_imp(list_mk_conj [`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = c983ri_family`;
                                    f4tm; unitE; posE; shape; phys; data; corner], concl0)) in
  let unit9, pos9, _, _ = c983ab_basics 8192 in
  let bt = let t = SPECL (c983ab_own 8192 @ [`x:real`; `y:real`]) C983BMO_TRANSLATED in
           let args = snd (strip_comb (lhs (concl t))) in [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args] in
  let toB = REWRITE_CONV[C983BMO_TRANSLATED] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  let viaB tm fact = EQ_MP (SYM (toB tm)) fact in
  let spec = SPECL (bt @ C983BMO_E @ [`t:real`]) F4BM_EXCLUDED in
  let ants = conjuncts (lhand (concl spec)) in
  let marker = c983ab_seed 9 `&2` `&457 / &500` in
  let bar = c983ab_mp C983AB_BOTTOM_ADVANCE in
  let f4 = CONV_RULE (REWRITE_CONV[c983e_actual; c983ri_owner_code] THENC ONCE_DEPTH_CONV EL_CONV)
             (ASSUME f4tm) in
  let westF = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (c983ab_point 4 f4) in
  let excl n pt =
    let d = REWRITE_RULE[ldisj] (c983ab_mp (oo_apart C983E_F 8192 n)) in
    let args = snd (strip_comb (concl pt)) in
    let d2 = SPECL [el 5 args; el 6 args] d in
    let a = lhand (rand (concl d2)) in
    NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) pt))) in
  let missingF = excl 2304 westF and missingSeed = excl 1 (ASSUME corner) in
  let disj =
    let d = REWRITE_RULE[ldisj] (c983ab_mp (oo_apart C983E_F 8192 512)) in
    let tm = list_mk_comb(`ldisj`, bt @ C983BMO_E) in
    EQ_MP (SYM ((REWRITE_CONV[ldisj; C983BMO_TRANSLATED; ASSUME phys]) tm))
          (GEN `x:real` (GEN `y:real` (SPECL [`x + &2`; `y + &2`] d))) in
  let facts = [unit9; pos9; ASSUME unitE; ASSUME posE; SYM (ASSUME shape); ASSUME data;
               marker; bar; missingF; missingSeed] in
  let prove_ant tm =
    if fst (strip_comb tm) = `ldisj` then disj else
    try find (fun f -> concl f = tm) facts with Failure _ ->
    let target = rhs (concl (toB tm)) in
    viaB tm (find (fun f -> aconv (concl f) target) facts) in
  let th = MP spec (end_itlist CONJ (map prove_ant ants)) in
  let th = EQ_MP (toB (concl th)) th in
  c983bmo_close (C983E_VARS @ C983BMO_E @ [`t:real`]) stmt th;;

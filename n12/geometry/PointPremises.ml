(* ========================================================================= *)
(* Port of Compact/Bridge/PointPremises.lean (N12Compact.PointPremises).     *)
(* Finite entry checks that mention only compulsory points.                  *)
(*   A Lean CertifiedPoint family (mask, point) is a theorem                 *)
(*     |- !c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP ..) = fam  *)
(*          ==> linside (ooc c1 c2 a b l mask) (oos ..) (oou ..) (oov ..) l x y *)
(*   (e.g. oo_inst fam (oo_seed mask (x, y)); its member field is in_fam).   *)
(*   Lean `Check d known inside outside` is decided by the producer below,   *)
(*   which for every allowed set owned of d derives each inside point from   *)
(*   queryInsidePoints d.mask 2 owned (oo_known: seeds and owned auxiliary   *)
(*   points) or from a known point of the same mask, and each outside point  *)
(*   from queryOutsidePoints d.mask 2 owned (missing markers, unowned        *)
(*   auxiliary points) or from a known point of another mask (disjointness). *)
(*   Lean `sound` is the producer                                            *)
(*     pp_sound (|- cdom fam m al) known inside outside                      *)
(*     |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = fam           *)
(*          ==> (linside (owner m) x1 y1 /\ ...) /\ (~linside (owner m) x1' y1' /\ ...) *)
(*   for literal point lists inside = [(x1, y1); ..], outside = [..] (an     *)
(*   empty list gives T).  A failure means the Lean Check would fail.        *)
(*   Tag pp_ / PP_.                                                          *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

let PP_VARS5 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

let pp_owner_lin m (x, y) =
  let mt = mk_small_numeral m in
  let own f = list_mk_comb(f, PP_VARS5 @ [mt]) in
  list_mk_comb(`linside`, map own [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`; x; y]);;

(* change the rational point coordinates of th to the literal ones of target *)
let pp_fix target th =
  if concl th = target then th else
  let c = ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
  EQ_MP (TRANS (c (concl th)) (SYM (c target))) th;;

let pp_conj ths = if ths = [] then TRUTH else end_itlist CONJ ths;;

(* the mask and point of an instantiated known-point theorem |- linside (owner k) x y *)
let pp_known_data th =
  let args = snd (strip_comb (concl th)) in
  (dest_small_numeral (rand (hd args)), (rat_of_term (el 5 args), rat_of_term (el 6 args)));;

(* Lean: sound *)
let pp_sound dom known inside outside =
  let fam = cdom_fam dom and m = cdom_mask dom in
  let mt = mk_small_numeral m in
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let h = ASSUME hyp in
  let hnp = CONJUNCT1 h and hrow = CONJUNCT2 h in
  let inm = in_fam m fam in
  let kn = map (fun th -> let t = MP (SPECL PP_VARS5 th) h in (pp_known_data t, t)) known in
  let memth = CONV_RULE (REWRITE_CONV[MEM]) (MATCH_MP CDOM_OWNER (CONJ dom (CONJ hnp (CONJ hrow inm)))) in
  let ins_t = map (pp_owner_lin m) inside in
  let outs_t = map (fun p -> mk_neg (pp_owner_lin m p)) outside in
  let goal = mk_conj((if ins_t = [] then `true` else list_mk_conj ins_t),
                     (if outs_t = [] then `true` else list_mk_conj outs_t)) in
  (* the theorem for one allowed set: eq is |- ooaux c1 c2 a b l m = S *)
  let case eq =
    let s = rhs (concl eq) in
    let ls = numset_of s in
    let inside_th (x, y) =
      let target = pp_owner_lin m (x, y) in
      let p = (rat_of_term x, rat_of_term y) in
      try let th = SPECL (PP_VARS5 @ [fam]) (oo_known m s (x, y)) in
          pp_fix target (MP th (CONJ hnp (CONJ hrow (CONJ inm eq))))
      with Failure _ ->
      try pp_fix target (snd (find (fun ((k, q), _) -> k = m && qeq p q) kn))
      with Failure _ -> failwith (Printf.sprintf "pp_sound %d: inside point (%s, %s) not certified for %s"
                          m (string_of_term x) (string_of_term y) (string_of_term s)) in
    let outside_th (x, y) =
      let target = mk_neg (pp_owner_lin m (x, y)) in
      let p = (rat_of_term x, rat_of_term y) in
      try let k = find (fun k -> not (mem k (bits m)) && qeq (marker_q k) p) (0 -- 15) in
          let th = SPECL (PP_VARS5 @ [fam]) (oo_missing m k) in
          pp_fix target (MP th (CONJ hnp (CONJ hrow inm)))
      with Failure _ ->
      try let j = find (fun j -> not (mem j ls) && qeq (aux2_point j) p) (0 -- 19) in
          let ath = SPEC mt (SPECL PP_VARS5 (oo_aux_point j)) in
          let e = TRANS ath (AP_TERM (rator (rand (concl ath))) eq) in
          let e2 = CONV_RULE (RAND_CONV OO_IN_CONV) e in
          pp_fix target (EQF_ELIM e2)
      with Failure _ ->
      try let ((k, _), _) = find (fun ((k, q), _) -> k <> m && qeq p q) kn in
          let thk = find (fun th -> fst (pp_known_data (MP (SPECL PP_VARS5 th) h)) = k &&
                                    qeq p (snd (pp_known_data (MP (SPECL PP_VARS5 th) h)))) known in
          pp_fix target (MP (SPECL PP_VARS5 (oo_excl fam m k thk)) h)
      with Failure _ -> failwith (Printf.sprintf "pp_sound %d: outside point (%s, %s) not certified for %s"
                          m (string_of_term x) (string_of_term y) (string_of_term s)) in
    let th = CONJ (pp_conj (map inside_th inside)) (pp_conj (map outside_th outside)) in
    if concl th = goal then th else failwith "pp_sound: goal mismatch" in
  let rec cases th =
    if is_disj (concl th) then
      let p, q = dest_disj (concl th) in
      DISJ_CASES th (case (ASSUME p)) (cases (ASSUME q))
    else if concl th = `false` then CONTR goal th
    else case th in
  GENL PP_VARS5 (DISCH hyp (cases memth));;

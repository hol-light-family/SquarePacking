(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/ActualOutwardFrame.lean.      *)
(* The actual reflected southeast frame of the C983 owner 5 (mask 512).     *)
(* Conventions of CP_OtherCases_C983_SharpApplications.ml.  The Lean         *)
(* existential OpenSquare r is the 5-tuple c' s' u' v' a' with its           *)
(* invariants (unit normal, 0 < a'); r.translated 2 2 is the tuple          *)
(* c' s' (u' - (c' * &2 + s' * &2)) (v' - (--s' * &2 + c' * &2)) a';         *)
(* pullY (owners p 5) is the LINSIDE_PULLY tuple; OutwardBarPoint.Faces is   *)
(* ocobp_faces; OutwardBarFrame.frame_original is OCOBF_FRAME_ORIGINAL.      *)
(* Tag C983AOF_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_SharpApplications.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarFrame.ml";;

(* Lean: southeast_outward_frame *)
let C983AOF_SOUTHEAST_OUTWARD_FRAME =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hyps = [c983f4f_mem 8 5; c983f4f_mem 18 5; mk_neg (c983f4f_mem 16 5)] in
  let marker = seed 5 `&47 / &20` `&33 / &20` in
  let corner = seed 2 `&3` `&1` and cornerMarker = seed 2 `&1543 / &500` `&1` in
  let facts = [unit 512; pos; side; marker; c983sa_aux 8 5; c983sa_aux 18 5; c983sa_missing 16 5;
               excl 512 16384 (seed 10 `&1543 / &500` `&2`); excl 512 12 corner;
               excl 512 12 cornerMarker; c983sa_bar_excl 512] in
  let py = c983fo_pull LINSIDE_PULLY 512 in
  let spec = SPECL py OCOBF_FRAME_ORIGINAL in
  (* discharge the antecedents up to C983FO_CONV, keep the conclusion as is *)
  let nf = map (CONV_RULE C983FO_CONV) facts in
  let pa tm =
    let eq = C983FO_CONV tm in
    let r = rhs (concl eq) in
    if r = `true` then EQT_ELIM eq else
    try EQ_MP (SYM eq) (find (fun f -> aconv (concl f) r) nf)
    with Failure _ -> failwith ("c983aof: " ^ string_of_term tm) in
  let th = MP spec (end_itlist CONJ (map pa (conjuncts (lhand (concl spec))))) in
  let concl_tm =
    let lin = list_mk_comb(`linside`, py @ [`x:real`; `y:real`]) in
    let q = [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] in
    let iff = list_mk_forall([`x:real`; `y:real`],
                mk_iff(list_mk_comb(`linside`, q @ [`x:real`; `y:real`]), lin)) in
    list_mk_exists(q, list_mk_conj
      [`c' * c' + s' * s' = &1`; `&0 < a'`; `&0 < c'`; `&0 <= s'`; `s' <= c'`; `(a':real) = l`; iff;
       `ocobp_faces c' s' (u' - (c' * &2 + s' * &2)) (v' - (--s' * &2 + c' * &2)) a'`]) in
  c983f4f_close (c983sa_stmt hyps concl_tm) th;;

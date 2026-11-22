(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/ActualOutwardPair.lean         *)
(* (N12Compact.Completion.OtherCases.C983).  The full actual C983 coupled-   *)
(* pair application.  Conventions of CP_OtherCases_C983_SharpApplications.ml *)
(* and CP_OtherCases_C983_ActualOutwardFrame.ml: owners p i is the owner at  *)
(* the literal mask (5 -> 512, 6 -> 1024, 7 -> 2304, 3 -> 48, 11 -> 32768),  *)
(* actual p i is c983e_actual c1 c2 a b l i.  q.translated 2 2 is the tuple  *)
(* c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a                   *)
(* (inside_translated_iff = C983AOP_TRANSLATE), pullY by LINSIDE_PULLY;      *)
(* SharpPointScalars.half_upper / half_lower OCSPS_HALF_UPPER / _LOWER,      *)
(* OutwardPair.impossible OCOP_IMPOSSIBLE, southeast_outward_point           *)
(* C983SA_SOUTHEAST_OUTWARD_POINT, southeast_outward_frame                   *)
(* C983AOF_SOUTHEAST_OUTWARD_FRAME; seed_inside / auxiliary_inside /         *)
(* owners_apart through c983fo_facts / c983sa_aux.  Tag C983AOP_.            *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_ActualOutwardFrame.ml";;
needs "n12/geometry/CP_OtherCases_OutwardPair.ml";;
needs "n12/geometry/CP_OtherCases_SharpPointScalars.ml";;

(* Lean: inside_translated_iff (used at offset 2 2) *)
let C983AOP_TRANSLATE = prove
 (`forall c s u v a x y. linside c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a x y <=>
                   linside c s u v a (x + &2) (y + &2)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: southeast_outward_pair_exclusion *)
let C983AOP_SOUTHEAST_OUTWARD_PAIR_EXCLUSION =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let own m = map (fun f -> list_mk_comb(f, C983E_VARS @ [mk_small_numeral m]))
                [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`] in
  let lin m x y = list_mk_comb(`linside`, own m @ [x; y]) in
  let top = lin 32768 `&2` `&3` in
  let hyps = [c983f4f_mem 8 5; c983f4f_mem 18 5; mk_neg (c983f4f_mem 16 5);
              c983f4f_mem 5 6; c983f4f_mem 17 6; top] in
  let northwest = seed 7 `&33 / &20` `&47 / &20` and corner = seed 3 `&3` `&3` in
  let facts = [unit 512; unit 1024; side; pos; seed 5 `&47 / &20` `&33 / &20`;
               seed 6 `&47 / &20` `&47 / &20`; c983sa_aux 5 6; c983sa_aux 17 6;
               excl 1024 2304 northwest; excl 1024 32768 (ASSUME top); excl 1024 48 corner;
               apart 512 1024] in
  let sub x y = mk_binop `(-):real->real->real` x y and add x y = mk_binop `(+):real->real->real` x y
  and mul x y = mk_binop `( * ):real->real->real` x y and neg x = mk_comb(`(--):real->real`, x) in
  let trans [c; s; u; v; a] =
    [c; s; sub u (add (mul c `&2`) (mul s `&2`)); sub v (add (mul (neg s) `&2`) (mul c `&2`)); a] in
  let c' = `c':real` and s' = `s':real` and u' = `u':real` and v' = `v':real` in
  let pully = [c'; neg s'; sub u' (mul `&4` s'); sub (sub (mul `&4` c') v') `l:real`; `l:real`] in
  prove(c983sa_stmt hyps `false`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY (fun th -> MP_TAC th) facts THEN
    MP_TAC(SPEC_ALL C983SA_SOUTHEAST_OUTWARD_POINT) THEN
    MP_TAC(SPEC_ALL C983AOF_SOUTHEAST_OUTWARD_FRAME) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
    STRIP_TAC THEN REPEAT DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a':real = l`)) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ocobp_faces]) THEN
    REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
    MP_TAC(SPECL [`c':real`; `s':real`; `&143 / &500`] OCSPS_HALF_UPPER) THEN
    MP_TAC(SPECL [`c':real`; `s':real`; `&37 / &50`] OCSPS_HALF_LOWER) THEN
    REWRITE_TAC[REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC OCOP_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC (trans pully @ trans (own 1024) @ [s']) THEN
    REWRITE_TAC[ldisj] THEN REWRITE_TAC[C983AOP_TRANSLATE] THEN REWRITE_TAC[LINSIDE_PULLY] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[LINSIDE_PULLY; REAL_SUB_SUB2] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

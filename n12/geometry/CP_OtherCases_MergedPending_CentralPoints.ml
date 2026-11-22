(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/CentralPoints.lean   *)
(* (namespace N12Compact.MergedPending; Lean header: "Source only,           *)
(* uncompiled").  Compulsory central points in the pending merged families. *)
(* Conventions of Families.ml / WallReach.ml: Case k is one of MPF_FAMILIES  *)
(* (c683, c700, c867) and per-case theorems are OCaml lists in that order;   *)
(* owner p m is the tuple (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l.     *)
(* auxPoints (auxKind kind) is AUXPTS kind (kind < 2).  SouthwestPoint.point *)
(* = CCSWP_POINT, C981CompletionCrosspoint.point = C981CP_POINT (applied to  *)
(* the pulled squares through the lemmas MPCP_RAW_CROSS_FIRST / _SECOND),  *)
(* MergedNearPoint.points_original = CCMNP_POINTS_ORIGINAL.  Lean's          *)
(* upper_merged_inward keeps its hypothesis 3072 IN family k (vacuous for    *)
(* c700).  Tag MPCP_.                                                        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_WallReach.ml";;
needs "n12/geometry/CP_CommonCases_MergedNearPoint.ml";;
needs "n12/geometry/CP_CommonCases_SouthwestPoint.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;

(* Lean: some_auxiliary (private; proved for every family) *)
let MPCP_SOME_AUXILIARY = OO_SOME_AUXILIARY;;

(* |- !k. k < n <=> k = n-1 \/ ... \/ k = 0 *)
let MPCP_LT_CASES =
  let tbl = Hashtbl.create 20 in
  fun n ->
    try Hashtbl.find tbl n with Not_found ->
    let k = `k:num` in
    let rec go m =
      if m = 0 then SPEC k (CONJUNCT1 LT) else
      let th1 = AP_TERM (mk_comb(`(<):num->num->bool`, k)) (num_CONV (mk_small_numeral m)) in
      let th2 = SPECL [k; mk_small_numeral (m - 1)] (CONJUNCT2 LT) in
      CONV_RULE (RAND_CONV (RAND_CONV (K (go (m - 1))))) (TRANS th1 th2) in
    let th = GEN k (REWRITE_RULE[] (go n)) in
    Hashtbl.add tbl n th; th;;

let MPCP_ENUM_TAC v n =
  let lt = mk_binop `(<):num->num->bool` v (mk_small_numeral n) in
  FIRST_ASSUM(fun th -> if concl th = lt then MP_TAC(EQ_MP (SPEC v (MPCP_LT_CASES n)) th) else NO_TAC) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Local pulled forms of the crosspoint lemma.                               *)
(* ------------------------------------------------------------------------- *)

let MPCP_RAW_TAC tuple =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL tuple C981CP_POINT) THEN
  REWRITE_TAC[LINSIDE_PULLSW; LINSIDE_PULLY; LINSIDE_PULLX] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC) THEN RASM_ARITH_TAC;
    REWRITE_TAC[]];;

(* the crosspoint lemma on pullY (pullX W) *)
let MPCP_RAW_CROSS_FIRST = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&2) (&87 / &50) /\ linside c s u v a (&87 / &50) (&2) /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\ ~linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&1) (&8 / &5) /\ ~linside c s u v a (&1) (&3 / &2)
     ==> linside c s u v a (&2) (&3 / &2)`,
  MPCP_RAW_TAC [`--c:real`; `--s:real`; `(u - &4 * c) - &4 * s`; `&4 * --c - (--v - a - &4 * s) - a`; `a:real`]);;

(* the crosspoint lemma on the pull by <true,true,true>: (x, y) |-> (4 - y, 4 - x) *)
let MPCP_RAW_CROSS_SECOND = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\
     linside c s u v a (&87 / &50) (&2) /\ linside c s u v a (&2) (&87 / &50) /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\ ~linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&8 / &5) (&1) /\ ~linside c s u v a (&3 / &2) (&1)
     ==> linside c s u v a (&3 / &2) (&2)`,
  MPCP_RAW_TAC [`--s:real`; `--c:real`; `(u - &4 * c) - &4 * s`;
                `--(&4 * --c - (--v - a - &4 * s) - a) - a`; `a:real`]);;

(* ------------------------------------------------------------------------- *)
(* Packing level.                                                            *)
(* ------------------------------------------------------------------------- *)

let mpcp_norm = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV);;
let mpcp_walls fam =
  let i = index fam MPF_FAMILIES in
  CONJUNCTS (REWRITE_RULE[mpf_wallData] (mpwr_inst fam (el i MPF_WALLS)));;
(* the coordinates of EL j (AUXPTS k) *)
let mpcp_pt k j =
  let th = (REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV)
             (mk_comb(mk_comb(`EL:num->(real^2)list->real^2`, mk_small_numeral j), mk_comb(`AUXPTS`, mk_small_numeral k))) in
  match dest_list (rand (rhs (concl th))) with [x; y] -> (x, y) | _ -> failwith "mpcp_pt";;
(* exclusions: owner m does not contain a point of owner n *)
let mpcp_excl fam m n th = mpcp_norm (mpwr_excl fam m n th);;
let mpcp_wall_x fam m n wall j k = mpcp_excl fam m n (mpwr_bar wall (fst (mpcp_pt k j)));;
let mpcp_wall_y fam m n wall j k = mpcp_excl fam m n (mpwr_bar wall (snd (mpcp_pt k j)));;
let mpcp_label fam m n j mem = mpcp_excl fam m n (mpwr_auxpt n j mem);;
let mpcp_unit m = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_UNIT) (mpwr_np `mpf_family_c700`);;

(* owner m contains one of its kind-k points; every point but the target is excluded *)
let mpcp_some_tac fam m k excls =
  let np = mpwr_np fam and img = CONJUNCT2 (ASSUME (mpwr_hyp fam)) in
  let kl = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral k) `2`)) in
  let ord = EQF_ELIM (AUXEX_CONV (mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral m),
                                          mk_comb(`auxex`, mk_small_numeral k)))) in
  let some = MP (SPECL (MPWR_VARS @ [fam; mk_small_numeral m; mk_small_numeral k]) MPCP_SOME_AUXILIARY)
               (end_itlist CONJ [np; img; in_fam m fam; kl; ord]) in
  MP_TAC some THEN DISCH_THEN(X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MPCP_ENUM_TAC `j:num` 10 THEN
  CONV_TAC(LAND_CONV(REWRITE_CONV[AUXPTS_EXPL.(k)] THENC ONCE_DEPTH_CONV EL_CONV THENC
                     REWRITE_CONV[VECTOR_2] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN
  REWRITE_TAC excls;;

(* Lean: southwest_points *)
let MPCP_SOUTHWEST_POINTS = map (fun fam ->
  let lab = mpwr_labels fam and w = mpcp_walls fam in
  let f = mpwr_auxpt 256 4 (el 0 lab) and g = mpwr_auxpt 256 13 (el 1 lab) in
  let mark = mpwr_seed fam 256 (`&33 / &20`, `&33 / &20`) in
  let left t = mpwr_excl fam 256 2 (mpwr_bar (el 1 w) t) and bottom t = mpwr_excl fam 256 1 (mpwr_bar (el 0 w) t) in
  let point = mpwr_apply fam 256 CCSWP_POINT
    [mark; f; g; left `&33 / &20`; bottom `&87 / &50`; bottom `&33 / &20`; left `&87 / &50`] in
  mpwr_prove fam (list_mk_conj [mpwr_inside 256 `&2` `&87 / &50`; mpwr_inside 256 `&87 / &50` `&2`;
                                mpwr_inside 256 `&39 / &20` `&39 / &20`])
    (end_itlist CONJ [f; g; point])) MPF_FAMILIES;;

(* Lean: southwest_crosspoints *)
let MPCP_SOUTHWEST_CROSSPOINTS = map2 (fun fam pts ->
  let w = mpcp_walls fam in
  let points = CONJUNCTS (mpwr_inst fam pts) in
  let mark = mpwr_seed fam 256 (`&33 / &20`, `&33 / &20`) in
  let north = mpwr_missing fam 256 11 and east = mpwr_missing fam 256 9 in
  let left t = mpwr_excl fam 256 2 (mpwr_bar (el 1 w) t) and bottom t = mpwr_excl fam 256 1 (mpwr_bar (el 0 w) t) in
  let first = mpwr_apply fam 256 MPCP_RAW_CROSS_FIRST
    [el 0 points; el 1 points; mark; north; east; left `&8 / &5`; left `&3 / &2`] in
  let second = mpwr_apply fam 256 MPCP_RAW_CROSS_SECOND
    [el 1 points; el 0 points; mark; east; north; bottom `&8 / &5`; bottom `&3 / &2`] in
  mpwr_prove fam (mk_conj(mpwr_inside 256 `&2` `&3 / &2`, mpwr_inside 256 `&3 / &2` `&2`))
    (CONJ first second)) MPF_FAMILIES MPCP_SOUTHWEST_POINTS;;

(* Lean: upper_merged_inward  (|- !c1 .. l. NPACK .. /\ IMAGE .. = family k /\ 3072 IN family k ==> ..) *)
let MPCP_UPPER_MERGED_INWARD = map (fun fam ->
  let tm = list_mk_forall(MPWR_VARS, mk_imp(list_mk_conj [`NPACK c1 c2 a b l`;
             mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam);
             mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `3072`), fam)],
             mpwr_inside 3072 `&2` `&113 / &50`)) in
  if rhs (concl (in_fam_conv 3072 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 3072 fam]) else
  let i = index fam MPF_FAMILIES in
  let lab = mpwr_labels fam and w = mpcp_walls fam in
  let se = MP (SPECL MPWR_VARS (el i MPD_SOUTHEAST_LOWER))
              (CONJ (mpwr_np fam) (CONJ (CONJUNCT2 (ASSUME (mpwr_hyp fam))) (in_fam 512 fam))) in
  let right = if i = 0 then mpcp_excl fam 3072 32 (mpwr_bar (mpwr_inst fam MPF_C683_RIGHT_SINGLETON) (snd (mpcp_pt 0 9)))
              else mpcp_label fam 3072 16384 9 (CONJUNCT1 (mpwr_inst fam MPD_C867_RIGHT_LABELS)) in
  let excls =
    [mpcp_wall_y fam 3072 2 (el 1 w) 0 0;
     mpcp_label fam 3072 4096 1 (el 2 lab);
     mpcp_wall_x fam 3072 1 (el 0 w) 2 0;
     mpcp_label fam 3072 32768 3 (el 6 lab);
     mpcp_label fam 3072 256 4 (el 0 lab);
     mpcp_label fam 3072 8192 6 (el 4 lab);
     mpcp_wall_x fam 3072 16 (el 2 w) 7 0;
     mpcp_label fam 3072 512 8 se;
     right] in
  let th = prove(mpwr_stmt fam (mpwr_inside 3072 `&2` `&113 / &50`),
    REPEAT GEN_TAC THEN DISCH_TAC THEN mpcp_some_tac fam 3072 0 excls) in
  prove(tm, MESON_TAC[th])) MPF_FAMILIES;;

(* Lean: c700_merged_elbow *)
let MPCP_C700_MERGED_ELBOW =
  let fam = `mpf_family_c700` in
  let lab = mpwr_labels fam and w = mpcp_walls fam in
  let rl = mpwr_inst fam MPD_C700_RIGHT_LABELS in
  let excls =
    [mpcp_wall_y fam 1536 2 (el 1 w) 0 1;
     mpcp_label fam 1536 4096 11 (el 3 lab);
     mpcp_wall_x fam 1536 1 (el 0 w) 2 1;
     mpcp_label fam 1536 256 13 (el 1 lab);
     mpcp_label fam 1536 32768 14 (el 7 lab);
     mpcp_label fam 1536 8192 15 (el 5 lab);
     mpcp_wall_x fam 1536 16 (el 2 w) 7 1;
     mpcp_label fam 1536 16384 18 (CONJUNCT2 rl);
     mpcp_excl fam 1536 32 (mpwr_bar (mpwr_inst fam MPF_C700_RIGHT_SINGLETON) (snd (mpcp_pt 1 9)))] in
  prove(mpwr_stmt fam (mpwr_inside 1536 `&113 / &50` `&2`),
    REPEAT GEN_TAC THEN DISCH_TAC THEN mpcp_some_tac fam 1536 1 excls);;

(* Lean: c700_merged_inward *)
let MPCP_C700_MERGED_INWARD =
  let fam = `mpf_family_c700` in
  let south = CONJUNCTS (mpwr_inst fam (el 1 MPCP_SOUTHWEST_POINTS)) in
  let marks = CONJUNCTS (mpwr_inst fam MPF_C700_MERGED_MARKERS) in
  let rl = mpwr_inst fam MPD_C700_RIGHT_LABELS in
  let right_f = mpwr_auxpt 16384 8 (CONJUNCT1 rl) in
  let right_marker = mpwr_seed fam 16384 (`&1543 / &500`, `&2`) in
  let single = mpwr_bar (mpwr_inst fam MPF_C700_RIGHT_SINGLETON) `&113 / &50` in
  let facts = map mpcp_norm
    ([mpcp_unit 1536; MP (SPECL MPWR_VARS OO_SIDE) (mpwr_np fam)] @ marks @
     [mpwr_excl fam 1536 256 (el 0 south); mpwr_excl fam 1536 16384 right_f;
      mpwr_excl fam 1536 32 single; mpwr_excl fam 1536 16384 right_marker;
      mpwr_excl fam 1536 256 (el 2 south)]) in
  prove(mpwr_stmt fam (mpwr_inside 1536 `&2` `&113 / &50`),
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(SPECL (butlast (mpwr_tuple 1536) @ [`l:real`]) CCMNP_POINTS_ORIGINAL) THEN
    REWRITE_TAC facts);;

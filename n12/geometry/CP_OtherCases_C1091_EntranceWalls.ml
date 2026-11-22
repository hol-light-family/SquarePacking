(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1091/EntranceWalls.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C1091.EntranceWalls).  The    *)
(* original C1091 wall signs and ordinary inward pairs.  owners p i is the   *)
(* owner at the literal mask EL i c1091od_masks (0 -> 1, 1 -> 12, 2 -> 48,   *)
(* 3 -> 192, 4 -> 258 (merged), 5 -> 512, 6 -> 1024, 7 -> 2048, 8 -> 4096,   *)
(* 9 -> 8192, 10 -> 16384, 11 -> 32768).  Frame fields: OO_SIDE / OO_BOX /   *)
(* oo_apart / c1091od_seed (EntranceFrame.frame = C1091EF_FRAME; h.mergedLow *)
(* = OC1091EML_ORIGINAL).  WallSignChord.chord = WSC_CHORD, incoming_pair =  *)
(* C1089WC_INCOMING_PAIR, EntranceDomains.* = C1091ED_*, ContinuousActual.   *)
(* southeast / northwest = C1089CA_SOUTHEAST / C1089CA_NORTHWEST (the family *)
(* q is c1091ef_owners).  pullX / pullY / pullSwap as in WallCore.ml.        *)
(* (Lean header: "Source only".)  Tag C1091EW_.                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_EntranceFrame.ml";;
needs "n12/geometry/CP_OtherCases_C1091_EntranceMergedLow.ml";;
needs "n12/geometry/CP_OtherCases_C1089_WallCore.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousActual.ml";;

let C1091EW_V = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let C1091EW_NP = `NPACK c1 c2 a b l` and C1091EW_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family`;;
let c1091ew_hh () = CONJ (ASSUME C1091EW_NP) (ASSUME C1091EW_IMG);;
let c1091ew_own m x y = list_mk_comb(`linside`,
  map (fun f -> list_mk_comb(f, C1091EW_V @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @
  [`l:real`; x; y]);;
let c1091ew_tuple m =
  map (fun f -> list_mk_comb(f, C1091EW_V @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1091ew_stmt vars hyps body =
  list_mk_forall(C1091EW_V @ vars, mk_imp(list_mk_conj ([C1091EW_NP; C1091EW_IMG] @ hyps), body));;
let c1091ew_lcy m = list_mk_comb(`lcy`, c1091ew_tuple m) and c1091ew_lcx m = list_mk_comb(`lcx`, c1091ew_tuple m);;
let c1091ew_le x y = mk_binop `(<=):real->real->bool` x y;;
let c1091ew_inst = c1089wc_inst and c1091ew_px = c1089wc_px and c1091ew_py = c1089wc_py
and c1091ew_sw = c1089wc_sw;;

(* basic owner facts: unit, unfolded box, side, all frame seeds *)
let C1091EW_SEEDS =
  [0, (`&28 / &25`, `&1`); 0, (`&87 / &50`, `&1`); 0, (`&187 / &100`, `&19 / &25`);
   1, (`&3`, `&1`); 1, (`&1543 / &500`, `&1`); 2, (`&3`, `&3`); 3, (`&1`, `&3`);
   3, (`&1`, `&1543 / &500`);
   4, (`&33 / &20`, `&33 / &20`); 5, (`&47 / &20`, `&33 / &20`); 6, (`&47 / &20`, `&47 / &20`);
   7, (`&33 / &20`, `&47 / &20`); 8, (`&457 / &500`, `&2`); 9, (`&2`, `&457 / &500`);
   10, (`&1543 / &500`, `&2`); 11, (`&2`, `&1543 / &500`)];;
let C1091EW_BASE_TAC ms =
  let np = ASSUME C1091EW_NP in
  MAP_EVERY (fun m ->
     let mt = mk_small_numeral m in
     ASSUME_TAC (MP (SPECL (C1091EW_V @ [mt]) OO_UNIT) np) THEN
     ASSUME_TAC (REWRITE_RULE[lcont] (MP (SPECL (C1091EW_V @ [mt]) OO_BOX) np))) ms THEN
  ASSUME_TAC (MP (SPECL C1091EW_V OO_SIDE) np) THEN
  MAP_EVERY (fun (i, p) -> ASSUME_TAC (MP (SPEC_ALL (c1091od_seed i p)) (c1091ew_hh ()))) C1091EW_SEEDS;;

(* add the conclusion of th (at vars) whose antecedent conjuncts are assumptions *)
let C1091EW_USE_TAC vars th (asl, w as g) =
  let th1 = SPECL vars th in
  let get t = try find (fun a -> aconv (concl a) t) (map snd asl)
              with Failure _ -> failwith ("C1091EW_USE_TAC: " ^ string_of_term t) in
  STRIP_ASSUME_TAC (MP th1 (end_itlist CONJ (map get (conjuncts (lhand (concl th1)))))) g;;

(* contradiction from two distinct owners containing the same point *)
let C1091EW_CLASH_TAC (asl, w as g) =
  let owned = List.filter_map (fun (_, th) ->
     let t = concl th in
     try let f, args = strip_comb t in
         if f <> `linside` then failwith "" else
         let m = dest_small_numeral (rand (hd args)) in
         Some (m, (el 5 args, el 6 args))
     with _ -> None) asl in
  let pairs = flat (map (fun (m, p) -> List.filter_map (fun (n, q) ->
     if m < n && aconv (fst p) (fst q) && aconv (snd p) (snd q) then Some (m, n, p) else None) owned)
     owned) in
  if pairs = [] then failwith "C1091EW_CLASH_TAC" else
  let (m, n, (x, y)) = hd pairs in
  let d = REWRITE_RULE[ldisj] (MP (SPECL C1091EW_V (oo_apart `c1091od_family` m n)) (c1091ew_hh ())) in
  (MP_TAC (SPECL [x; y] d) THEN ASM_REWRITE_TAC[]) g;;

let C1091EW_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[lcont] THEN FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C1091EW_CLASH_TAC;
         REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_ASSUM(fun b -> MP_TAC (MATCH_MP b th))) THEN
           REAL_ARITH_TAC;
         FIRST_ASSUM(fun th -> if is_disj (concl th) then MP_TAC th THEN CONV_TAC TAUT else NO_TAC);
         REWRITE_TAC[lcx; lcy] THEN RASM_ARITH_TAC;
         RASM_ARITH_TAC];;

let C1091EW_APPLY_TAC th =
  MP_TAC th THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN C1091EW_SIDE_TAC; CONV_TAC TAUT];;

let c1091ew_chord tuple r = c1091ew_inst WSC_CHORD (tuple @ [r]);;
let C1091EW_CHORD_TAC m th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [m] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[lcx; lcy]) THEN C1091EW_APPLY_TAC th;;

(* chord facts  th (vars @ [t])  for the listed coordinates t *)
let C1091EW_CHORDS_TAC th ts =
  MAP_EVERY (fun t -> MP_TAC (SPECL (C1091EW_V @ [t]) th) THEN
                      CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
                      DISCH_TAC) ts;;
let C1091EW_COVERS_TAC ths =
  MAP_EVERY (fun th -> ASSUME_TAC (MP (SPEC_ALL th) (c1091ew_hh ()))) ths;;

(* Lean: left_high *)
let C1091EW_LEFT_HIGH = prove
 (c1091ew_stmt [`y:real`] [c1091ew_le `&2` (c1091ew_lcy 4096);
                           `&111 / &50 <= y`; `y <= &239 / &100`] (c1091ew_own 4096 `&1` `y:real`),
  C1091EW_CHORD_TAC 4096 (c1091ew_chord (c1091ew_tuple 4096) `y:real`));;

(* Lean: left_low *)
let C1091EW_LEFT_LOW = prove
 (c1091ew_stmt [`y:real`] [c1091ew_le (c1091ew_lcy 4096) `&2`;
                           `&161 / &100 <= y`; `y <= &89 / &50`] (c1091ew_own 4096 `&1` `y:real`),
  C1091EW_CHORD_TAC 4096 (c1091ew_chord (c1091ew_py (c1091ew_tuple 4096)) `&4 - y`));;

(* Lean: right_high *)
let C1091EW_RIGHT_HIGH = prove
 (c1091ew_stmt [`y:real`] [c1091ew_le `&2` (c1091ew_lcy 16384);
                           `&111 / &50 <= y`; `y <= &239 / &100`] (c1091ew_own 16384 `&3` `y:real`),
  C1091EW_CHORD_TAC 16384 (c1091ew_chord (c1091ew_px (c1091ew_tuple 16384)) `y:real`));;

(* Lean: right_low *)
let C1091EW_RIGHT_LOW = prove
 (c1091ew_stmt [`y:real`] [c1091ew_le (c1091ew_lcy 16384) `&2`;
                           `&161 / &100 <= y`; `y <= &89 / &50`] (c1091ew_own 16384 `&3` `y:real`),
  C1091EW_CHORD_TAC 16384
    (c1091ew_chord (c1091ew_py (c1091ew_px (c1091ew_tuple 16384))) `&4 - y`));;

(* Lean: top_high *)
let C1091EW_TOP_HIGH = prove
 (c1091ew_stmt [`x:real`] [c1091ew_le `&2` (c1091ew_lcx 32768);
                           `&111 / &50 <= x`; `x <= &239 / &100`] (c1091ew_own 32768 `x:real` `&3`),
  C1091EW_CHORD_TAC 32768
    (c1091ew_chord (c1091ew_sw (c1091ew_py (c1091ew_tuple 32768))) `x:real`));;

(* Lean: top_low *)
let C1091EW_TOP_LOW = prove
 (c1091ew_stmt [`x:real`] [c1091ew_le (c1091ew_lcx 32768) `&2`;
                           `&161 / &100 <= x`; `x <= &89 / &50`] (c1091ew_own 32768 `x:real` `&3`),
  C1091EW_CHORD_TAC 32768
    (c1091ew_chord (c1091ew_sw (c1091ew_py (c1091ew_px (c1091ew_tuple 32768)))) `&4 - x`));;

(* Lean: incoming_pair (abbrev of C1089.WallCore.incoming_pair) *)
let C1091EW_INCOMING_PAIR = C1089WC_INCOMING_PAIR;;

(* Lean: northwest_inward *)
let C1091EW_NORTHWEST_INWARD = prove
 (c1091ew_stmt [] [c1091ew_le `&2` (c1091ew_lcy 4096); c1091ew_le (c1091ew_lcx 32768) `&2`]
    (mk_conj(c1091ew_own 2048 `&2` `&113 / &50`, c1091ew_own 2048 `&87 / &50` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [2048] THEN
  C1091EW_COVERS_TAC [C1091ED_NORTHWEST_F; C1091ED_NORTHWEST_G] THEN
  C1091EW_CHORDS_TAC C1091EW_LEFT_HIGH [`&113 / &50`; `&239 / &100`] THEN
  C1091EW_CHORDS_TAC C1091EW_TOP_LOW [`&87 / &50`; `&161 / &100`] THEN
  C1091EW_APPLY_TAC (SPECL (c1091ew_tuple 2048) C1091EW_INCOMING_PAIR));;

(* Lean: northeast_inward *)
let C1091EW_NORTHEAST_INWARD = prove
 (c1091ew_stmt [] [c1091ew_le `&2` (c1091ew_lcy 16384); c1091ew_le `&2` (c1091ew_lcx 32768)]
    (mk_conj(c1091ew_own 1024 `&2` `&113 / &50`, c1091ew_own 1024 `&113 / &50` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [1024] THEN
  C1091EW_COVERS_TAC [C1091ED_NORTHEAST_F; C1091ED_NORTHEAST_G] THEN
  C1091EW_CHORDS_TAC C1091EW_RIGHT_HIGH [`&113 / &50`; `&239 / &100`] THEN
  C1091EW_CHORDS_TAC C1091EW_TOP_HIGH [`&113 / &50`; `&239 / &100`] THEN
  C1091EW_APPLY_TAC (c1091ew_inst C1091EW_INCOMING_PAIR (c1091ew_px (c1091ew_tuple 1024))));;

(* Lean: southeast_inward *)
let C1091EW_SOUTHEAST_INWARD = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`]
    (mk_conj(c1091ew_own 512 `&2` `&87 / &50`, c1091ew_own 512 `&113 / &50` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [512] THEN
  C1091EW_COVERS_TAC [C1091ED_SOUTHEAST_F; C1091ED_SOUTHEAST_G] THEN
  MP_TAC (MP (SPEC_ALL C1091ED_BOTTOM_BAR) (c1091ew_hh ())) THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MAP_EVERY (fun x -> MP_TAC (SPEC x th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
                             REWRITE_TAC[] THEN DISCH_TAC) [`&113 / &50`; `&239 / &100`]
    else NO_TAC) THEN
  C1091EW_CHORDS_TAC C1091EW_RIGHT_LOW [`&87 / &50`; `&161 / &100`] THEN
  C1091EW_APPLY_TAC (c1091ew_inst C1091EW_INCOMING_PAIR (c1091ew_sw (c1091ew_tuple 512))));;

(* Lean: left_above *)
let C1091EW_LEFT_ABOVE = prove
 (c1091ew_stmt [] [] (mk_binop `(<):real->real->bool` `&2` (c1091ew_lcy 4096)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ASSUME_TAC (MP (SPEC_ALL OC1091EML_ORIGINAL) (c1091ew_hh ())) THEN
  C1091EW_CHORDS_TAC C1091EW_LEFT_LOW [`&87 / &50`] THEN
  C1091EW_CLASH_TAC);;

(* apply a ContinuousActual lemma to the packing's owners c1091ef_owners *)
let C1091EW_CONTINUOUS_TAC th =
  MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)
           (REWRITE_RULE[c1091ef_frame] (MP (SPEC_ALL C1091EF_FRAME) (c1091ew_hh ())))) THEN
  DISCH_THEN(fun fr ->
    let frs = CONJUNCTS fr in
    MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV) (SPECL c1091ef_owners th)) THEN ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST [FIRST (map ACCEPT_TAC frs);
             REWRITE_TAC[] THEN NO_TAC;
             GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC OO_UNIT THEN FIRST_ASSUM ACCEPT_TAC;
             ALL_TAC] THEN
      CONV_TAC C1091EF_EL_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC C1091EF_EL_CONV THEN REWRITE_TAC[]]);;

(* Lean: southeast_center *)
let C1091EW_SOUTHEAST_CENTER = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`]
    (mk_conj(c1091ew_own 512 `&2` `&2`, c1091ew_own 16384 `&3` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [] THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_SOUTHEAST_INWARD THEN
  C1091EW_CHORDS_TAC C1091EW_RIGHT_LOW [`&87 / &50`] THEN
  ASSUME_TAC (MP (SPEC_ALL C1091ED_BOTTOM_FAR) (c1091ew_hh ())) THEN
  C1091EW_CONTINUOUS_TAC C1089CA_SOUTHEAST);;

(* Lean: northwest_center *)
let C1091EW_NORTHWEST_CENTER = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcx 32768) `&2`]
    (mk_conj(c1091ew_own 2048 `&2` `&2`, c1091ew_own 32768 `&2` `&3`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1091EW_BASE_TAC [] THEN
  ASSUME_TAC (MATCH_MP REAL_LT_IMP_LE (MP (SPEC_ALL C1091EW_LEFT_ABOVE) (c1091ew_hh ()))) THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_NORTHWEST_INWARD THEN
  C1091EW_CHORDS_TAC C1091EW_TOP_LOW [`&87 / &50`] THEN
  STRIP_ASSUME_TAC (MP (SPEC_ALL C1091ED_LEFT_PAIR) (c1091ew_hh ())) THEN
  ASSUME_TAC (MP (SPEC_ALL OC1091EML_ORIGINAL) (c1091ew_hh ())) THEN
  C1091EW_CONTINUOUS_TAC C1089CA_NORTHWEST);;

(* Lean: right_low_top_low_impossible *)
let C1091EW_RIGHT_LOW_TOP_LOW_IMPOSSIBLE = prove
 (c1091ew_stmt [] [c1091ew_le (c1091ew_lcy 16384) `&2`; c1091ew_le (c1091ew_lcx 32768) `&2`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_SOUTHEAST_CENTER THEN
  C1091EW_USE_TAC C1091EW_V C1091EW_NORTHWEST_CENTER THEN
  C1091EW_CLASH_TAC);;

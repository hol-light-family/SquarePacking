(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/WallCore.lean                 *)
(* (namespace N12Compact.Completion.OtherCases.C1089.WallCore).  C1089's     *)
(* actual wall chords and incoming central pairs.  Conventions of            *)
(* OriginalData.ml / DirectDomains.ml: owners p i = owner (EL i              *)
(* c1089sc_masks), written with the literal mask (0 -> 1, 1 -> 12, 2 -> 48,  *)
(* 3 -> 192, 4 -> 256, 5 -> 512, 6 -> 1024, 7 -> 2048, 8 -> 4096, 9 -> 8192, *)
(* 10 -> 16384, 11 -> 32768).  The Frame fields used (side, box, apart,      *)
(* markers, singleton seeds, corners) are OO_SIDE / OO_BOX / oo_apart /      *)
(* c1089od_seed.  centerX / centerY = lcx / lcy; pullX / pullY / pullSwap    *)
(* tuples as in p2_base (LINSIDE_PULLX / Y / SW).  Used:                     *)
(* ContinuousBottom.reach_of_far = C1089CB_REACH_OF_FAR, WallSignChord.chord *)
(* = WSC_CHORD, C1092CornerTwoGaps.impossible = C1092CTG_IMPOSSIBLE,         *)
(* C1092MixedSpan.impossible = C1092MS_IMPOSSIBLE, AuxiliaryCover.*_cover =  *)
(* C1089AC_* (EL masks evaluated), DirectDomains.bottom_far =                *)
(* C1089DD_BOTTOM_FAR, horizontal_segment = OO_HORIZONTAL_SEGMENT.           *)
(* An OpenSquare q is c s u v a with unit normal and positive side explicit. *)
(* (Lean header: "Source only, uncompiled".)  Tag C1089WC_.                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_DirectDomains.ml";;
needs "n12/geometry/CP_OtherCases_C1089_AuxiliaryCover.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;
needs "n12/geometry/CP_C1092_CornerTwoGaps.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/WallSignChord.ml";;

let C1089WC_V = C1089SC_VARS;;
let C1089WC_NP = `NPACK c1 c2 a b l` and C1089WC_IMG = `IMAGE binarysum (FFP c1 c2 a b l) = c1089sc_family`;;
let c1089wc_hh () = CONJ (ASSUME C1089WC_NP) (ASSUME C1089WC_IMG);;
let c1089wc_own = c1089dd_own;;
let c1089wc_tuple m =
  map (fun f -> list_mk_comb(f, C1089WC_V @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c1089wc_stmt vars hyps body =
  list_mk_forall(C1089WC_V @ vars, mk_imp(list_mk_conj ([C1089WC_NP; C1089WC_IMG] @ hyps), body));;
let C1089WC_MASKS = [1; 12; 48; 192; 256; 512; 1024; 2048; 4096; 8192; 16384; 32768];;

(* pulled tuples *)
let c1089wc_sub tms t = match t with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms
  | _ -> failwith "c1089wc_sub";;
let c1089wc_px = c1089wc_sub [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;
let c1089wc_py = c1089wc_sub [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let c1089wc_sw = c1089wc_sub [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;
let C1089WC_PULL_CONV =
  REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW; REAL_NEG_MUL2] THENC
  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV THENC REWRITE_CONV[REAL_SUB_SUB2];;
let c1089wc_inst th tms = CONV_RULE C1089WC_PULL_CONV (SPECL tms th);;

(* EL i c1089sc_masks -> literal mask *)
let c1089wc_lit th = CONV_RULE (REWRITE_CONV[c1089sc_masks] THENC ONCE_DEPTH_CONV EL_CONV) th;;

(* basic owner facts: unit, unfolded box, side, all frame seeds *)
let C1089WC_SEEDS =
  [0, (`&28 / &25`, `&1`); 0, (`&87 / &50`, `&1`); 0, (`&187 / &100`, `&19 / &25`);
   1, (`&3`, `&1`); 2, (`&3`, `&3`); 3, (`&1`, `&3`);
   4, (`&33 / &20`, `&33 / &20`); 5, (`&47 / &20`, `&33 / &20`); 6, (`&47 / &20`, `&47 / &20`);
   7, (`&33 / &20`, `&47 / &20`); 8, (`&457 / &500`, `&2`); 9, (`&2`, `&457 / &500`);
   10, (`&1543 / &500`, `&2`); 11, (`&2`, `&1543 / &500`)];;
let C1089WC_BASE_TAC ms =
  let np = ASSUME C1089WC_NP in
  MAP_EVERY (fun m ->
     let mt = mk_small_numeral m in
     ASSUME_TAC (MP (SPECL (C1089WC_V @ [mt]) OO_UNIT) np) THEN
     ASSUME_TAC (REWRITE_RULE[lcont] (MP (SPECL (C1089WC_V @ [mt]) OO_BOX) np))) ms THEN
  ASSUME_TAC (MP (SPECL C1089WC_V OO_SIDE) np) THEN
  MAP_EVERY (fun (i, p) -> ASSUME_TAC (MP (SPEC_ALL (c1089od_seed i p)) (c1089wc_hh ()))) C1089WC_SEEDS;;

(* add the conclusion of th (at vars) whose antecedent conjuncts are assumptions *)
let C1089WC_USE_TAC vars th (asl, w as g) =
  let th1 = SPECL vars th in
  let get t = try find (fun a -> aconv (concl a) t) (map snd asl)
              with Failure _ -> failwith ("C1089WC_USE_TAC: " ^ string_of_term t) in
  STRIP_ASSUME_TAC (MP th1 (end_itlist CONJ (map get (conjuncts (lhand (concl th1)))))) g;;

(* contradiction from two distinct owners containing the same point *)
let C1089WC_CLASH_TAC (asl, w as g) =
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
  if pairs = [] then failwith "C1089WC_CLASH_TAC" else
  let (m, n, (x, y)) = hd pairs in
  let d = REWRITE_RULE[ldisj] (MP (SPECL C1089WC_V (oo_apart `c1089sc_family` m n)) (c1089wc_hh ())) in
  (MP_TAC (SPECL [x; y] d) THEN ASM_REWRITE_TAC[]) g;;

let C1089WC_SIDE_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[lcont] THEN FIRST_ASSUM ACCEPT_TAC;
         DISCH_TAC THEN C1089WC_CLASH_TAC;
         REPEAT GEN_TAC THEN DISCH_THEN(fun th -> FIRST_ASSUM(fun b -> MP_TAC (MATCH_MP b th))) THEN
           REAL_ARITH_TAC;
         FIRST_ASSUM(fun th -> if is_disj (concl th) then MP_TAC th THEN CONV_TAC TAUT else NO_TAC);
         REWRITE_TAC[lcx; lcy] THEN RASM_ARITH_TAC;
         RASM_ARITH_TAC];;

(* apply a (pulled) lemma instance to the goal: MP, discharge, close *)
let C1089WC_APPLY_TAC th =
  MP_TAC th THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN C1089WC_SIDE_TAC; CONV_TAC TAUT];;
let C1089WC_REFUTE_TAC th =
  MATCH_MP_TAC (if is_neg (concl th) then NOT_ELIM th else th) THEN REPEAT CONJ_TAC THEN C1089WC_SIDE_TAC;;

(* Lean: singleton_bar *)
let C1089WC_SINGLETON_BAR = prove
 (c1089wc_stmt [`x:real`] [`&28 / &25 <= x`; `x <= &87 / &50`] (c1089wc_own 1 `x:real` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [] THEN
  MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&28 / &25`; `&87 / &50`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: bottom *)
let C1089WC_BOTTOM = prove
 (c1089wc_stmt [] []
    (list_mk_conj [`&51 / &25 < lcx (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192) (oov c1 c2 a b l 8192) l`;
                   c1089wc_own 8192 `&14 / &5` `&1`;
                   mk_forall(`x:real`, mk_imp(`&113 / &50 <= x`, mk_imp(`x <= &14 / &5`,
                     c1089wc_own 8192 `x:real` `&1`)))]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [8192] THEN
  C1089WC_USE_TAC C1089WC_V C1089DD_BOTTOM_FAR THEN
  REWRITE_TAC[IMP_IMP] THEN
  C1089WC_APPLY_TAC (SPECL (c1089wc_tuple 8192) C1089CB_REACH_OF_FAR));;

let c1089wc_chord tuple r = c1089wc_inst WSC_CHORD (tuple @ [r]);;
let c1089wc_lcy m = list_mk_comb(`lcy`, c1089wc_tuple m) and c1089wc_lcx m = list_mk_comb(`lcx`, c1089wc_tuple m);;
let C1089WC_CHORD_TAC m th =
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [m] THEN
  RULE_ASSUM_TAC (REWRITE_RULE[lcx; lcy]) THEN C1089WC_APPLY_TAC th;;

(* Lean: left_high *)
let C1089WC_LEFT_HIGH = prove
 (c1089wc_stmt [`y:real`] [mk_binop `(<=):real->real->bool` `&2` (c1089wc_lcy 4096);
                           `&111 / &50 <= y`; `y <= &239 / &100`] (c1089wc_own 4096 `&1` `y:real`),
  C1089WC_CHORD_TAC 4096 (c1089wc_chord (c1089wc_tuple 4096) `y:real`));;

(* Lean: left_low *)
let C1089WC_LEFT_LOW = prove
 (c1089wc_stmt [`y:real`] [mk_binop `(<=):real->real->bool` (c1089wc_lcy 4096) `&2`;
                           `&161 / &100 <= y`; `y <= &89 / &50`] (c1089wc_own 4096 `&1` `y:real`),
  C1089WC_CHORD_TAC 4096 (c1089wc_chord (c1089wc_py (c1089wc_tuple 4096)) `&4 - y`));;

(* Lean: right_high *)
let C1089WC_RIGHT_HIGH = prove
 (c1089wc_stmt [`y:real`] [mk_binop `(<=):real->real->bool` `&2` (c1089wc_lcy 16384);
                           `&111 / &50 <= y`; `y <= &239 / &100`] (c1089wc_own 16384 `&3` `y:real`),
  C1089WC_CHORD_TAC 16384 (c1089wc_chord (c1089wc_px (c1089wc_tuple 16384)) `y:real`));;

(* Lean: right_low *)
let C1089WC_RIGHT_LOW = prove
 (c1089wc_stmt [`y:real`] [mk_binop `(<=):real->real->bool` (c1089wc_lcy 16384) `&2`;
                           `&161 / &100 <= y`; `y <= &89 / &50`] (c1089wc_own 16384 `&3` `y:real`),
  C1089WC_CHORD_TAC 16384
    (c1089wc_chord (c1089wc_py (c1089wc_px (c1089wc_tuple 16384))) `&4 - y`));;

(* Lean: top_high *)
let C1089WC_TOP_HIGH = prove
 (c1089wc_stmt [`x:real`] [mk_binop `(<=):real->real->bool` `&2` (c1089wc_lcx 32768);
                           `&111 / &50 <= x`; `x <= &239 / &100`] (c1089wc_own 32768 `x:real` `&3`),
  C1089WC_CHORD_TAC 32768
    (c1089wc_chord (c1089wc_sw (c1089wc_py (c1089wc_tuple 32768))) `x:real`));;

(* Lean: top_low *)
let C1089WC_TOP_LOW = prove
 (c1089wc_stmt [`x:real`] [mk_binop `(<=):real->real->bool` (c1089wc_lcx 32768) `&2`;
                           `&161 / &100 <= x`; `x <= &89 / &50`] (c1089wc_own 32768 `x:real` `&3`),
  C1089WC_CHORD_TAC 32768
    (c1089wc_chord (c1089wc_sw (c1089wc_py (c1089wc_px (c1089wc_tuple 32768)))) `&4 - x`));;

(* Lean: incoming_pair *)
let C1089WC_INCOMING_PAIR = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     (linside c s u v a (&1) (&113 / &50) \/ linside c s u v a (&8 / &5) (&3) \/
      linside c s u v a (&2) (&113 / &50)) /\
     (linside c s u v a (&1) (&12 / &5) \/ linside c s u v a (&87 / &50) (&2) \/
      linside c s u v a (&87 / &50) (&3)) /\
     ~linside c s u v a (&1) (&113 / &50) /\ ~linside c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&161 / &100) (&3) /\ ~linside c s u v a (&1) (&239 / &100) /\
     ~linside c s u v a (&1) (&3)
     ==> linside c s u v a (&2) (&113 / &50) /\ linside c s u v a (&87 / &50) (&2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  let q = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] in
  let i1 = c1089wc_inst C1092CTG_IMPOSSIBLE (c1089wc_px q @ [`&39 / &100`; `&39 / &100`])
  and i2 = c1089wc_inst C1092MS_IMPOSSIBLE (c1089wc_sw q)
  and i3 = c1089wc_inst C1092MS_IMPOSSIBLE (c1089wc_py (c1089wc_px q)) in
  SUBGOAL_THEN `s * s + c * c = &1` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC i1 THEN MP_TAC i2 THEN MP_TAC i3 THEN ASM_REWRITE_TAC[] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN CONV_TAC TAUT);;

(* add chord facts  th (vars @ [t])  for the listed coordinates t *)
let C1089WC_CHORDS_TAC th ts =
  MAP_EVERY (fun t -> MP_TAC (SPECL (C1089WC_V @ [t]) th) THEN
                      CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN ASM_REWRITE_TAC[] THEN
                      DISCH_TAC) ts;;
let C1089WC_COVERS_TAC ths =
  MAP_EVERY (fun th -> ASSUME_TAC (MP (SPEC_ALL (c1089wc_lit th)) (c1089wc_hh ()))) ths;;

(* Lean: northwest_inward *)
let C1089WC_NORTHWEST_INWARD = prove
 (c1089wc_stmt [] [mk_binop `(<=):real->real->bool` `&2` (c1089wc_lcy 4096);
                   mk_binop `(<=):real->real->bool` (c1089wc_lcx 32768) `&2`]
    (mk_conj(c1089wc_own 2048 `&2` `&113 / &50`, c1089wc_own 2048 `&87 / &50` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [2048] THEN
  C1089WC_COVERS_TAC [C1089AC_NORTHWEST_F_COVER; C1089AC_NORTHWEST_G_COVER] THEN
  C1089WC_CHORDS_TAC C1089WC_LEFT_HIGH [`&113 / &50`; `&239 / &100`] THEN
  C1089WC_CHORDS_TAC C1089WC_TOP_LOW [`&87 / &50`; `&161 / &100`] THEN
  C1089WC_APPLY_TAC (SPECL (c1089wc_tuple 2048) C1089WC_INCOMING_PAIR));;

(* Lean: northeast_inward *)
let C1089WC_NORTHEAST_INWARD = prove
 (c1089wc_stmt [] [mk_binop `(<=):real->real->bool` `&2` (c1089wc_lcy 16384);
                   mk_binop `(<=):real->real->bool` `&2` (c1089wc_lcx 32768)]
    (mk_conj(c1089wc_own 1024 `&2` `&113 / &50`, c1089wc_own 1024 `&113 / &50` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [1024] THEN
  C1089WC_COVERS_TAC [C1089AC_NORTHEAST_F_COVER; C1089AC_NORTHEAST_G_COVER] THEN
  C1089WC_CHORDS_TAC C1089WC_RIGHT_HIGH [`&113 / &50`; `&239 / &100`] THEN
  C1089WC_CHORDS_TAC C1089WC_TOP_HIGH [`&113 / &50`; `&239 / &100`] THEN
  C1089WC_APPLY_TAC (c1089wc_inst C1089WC_INCOMING_PAIR (c1089wc_px (c1089wc_tuple 1024))));;

(* Lean: southeast_inward *)
let C1089WC_SOUTHEAST_INWARD = prove
 (c1089wc_stmt [] [mk_binop `(<=):real->real->bool` (c1089wc_lcy 16384) `&2`]
    (mk_conj(c1089wc_own 512 `&2` `&87 / &50`, c1089wc_own 512 `&113 / &50` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [512] THEN
  C1089WC_COVERS_TAC [C1089AC_SOUTHEAST_F_COVER; C1089AC_SOUTHEAST_G_COVER] THEN
  C1089WC_USE_TAC C1089WC_V C1089WC_BOTTOM THEN
  FIRST_X_ASSUM(fun th -> if is_forall (concl th) && can (find_term ((=) `&14 / &5`)) (concl th)
    then MAP_EVERY (fun x -> MP_TAC (SPEC x th) THEN CONV_TAC (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
                             REWRITE_TAC[] THEN DISCH_TAC) [`&113 / &50`; `&239 / &100`]
    else NO_TAC) THEN
  C1089WC_CHORDS_TAC C1089WC_RIGHT_LOW [`&87 / &50`; `&161 / &100`] THEN
  C1089WC_APPLY_TAC (c1089wc_inst C1089WC_INCOMING_PAIR (c1089wc_sw (c1089wc_tuple 512))));;

(* Lean: southwest_inward *)
let C1089WC_SOUTHWEST_INWARD = prove
 (c1089wc_stmt [] [mk_binop `(<=):real->real->bool` (c1089wc_lcy 4096) `&2`]
    (mk_conj(c1089wc_own 256 `&2` `&87 / &50`, c1089wc_own 256 `&87 / &50` `&2`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1089WC_BASE_TAC [256] THEN
  C1089WC_COVERS_TAC [C1089AC_SOUTHWEST_F_COVER; C1089AC_SOUTHWEST_G_COVER] THEN
  C1089WC_CHORDS_TAC C1089WC_LEFT_LOW [`&87 / &50`] THEN
  C1089WC_CHORDS_TAC C1089WC_SINGLETON_BAR [`&8 / &5`] THEN
  let c1089wc_disj3 l = list_mk_disj (map (fun (x, y) -> c1089wc_own 256 x y) l) in
  let c1089wc_fcov_tm = c1089wc_disj3 [`&1`, `&87 / &50`; `&8 / &5`, `&1`; `&2`, `&87 / &50`]
  and c1089wc_gcov_tm = c1089wc_disj3 [`&1`, `&8 / &5`; `&87 / &50`, `&1`; `&87 / &50`, `&2`] in
  SUBGOAL_THEN (c1089wc_own 256 `&2` `&87 / &50`) ASSUME_TAC THENL
   [MP_TAC (ASSUME c1089wc_fcov_tm) THEN STRIP_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN C1089WC_CLASH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REFUTE_THEN ASSUME_TAC THEN
  SUBGOAL_THEN (c1089wc_own 256 `&1` `&8 / &5`) ASSUME_TAC THENL
   [MP_TAC (ASSUME c1089wc_gcov_tm) THEN STRIP_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    TRY C1089WC_CLASH_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  C1089WC_REFUTE_TAC (c1089wc_inst C1092MS_IMPOSSIBLE (c1089wc_px (c1089wc_tuple 256))));;

(* Lean: two_low_impossible *)
let C1089WC_TWO_LOW_IMPOSSIBLE = prove
 (c1089wc_stmt [] [mk_binop `(<=):real->real->bool` (c1089wc_lcy 4096) `&2`;
                   mk_binop `(<=):real->real->bool` (c1089wc_lcy 16384) `&2`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C1089WC_USE_TAC C1089WC_V C1089WC_SOUTHWEST_INWARD THEN
  C1089WC_USE_TAC C1089WC_V C1089WC_SOUTHEAST_INWARD THEN
  C1089WC_CLASH_TAC);;

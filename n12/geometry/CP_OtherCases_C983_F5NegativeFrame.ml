(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F5NegativeFrame.lean           *)
(* (N12Compact.Completion.OtherCases.C983).  Whole original-owner sign       *)
(* reduction after the F5 upper-right entrance.  Conventions of              *)
(* CP_OtherCases_C983_LeftOrigin.ml: owners p 5 / 6 / 7 / 8 / 9 / 10 =       *)
(* owner 512 / 1024 / 2304 / 4096 / 8192 / 16384, actual p i =               *)
(* c983e_actual c1 c2 a b l i; q.translated 2 2 is the tuple                 *)
(* (c, s, u - (c * &2 + s * &2), v - (--s * &2 + c * &2), a)                  *)
(* (CCIP_INSIDE_TRANSLATED).  ClosedFrames.canonical_frame                   *)
(* CLF_CANONICAL_FRAME; PositiveEnding.nonnegative_impossible                *)
(* OCPEND_NONNEGATIVE_IMPOSSIBLE; InwardSign.positive_impossible             *)
(* OCISG_POSITIVE_IMPOSSIBLE; f5_merged_center C983MCF_F5_MERGED_CENTER;     *)
(* f5_southeast_g6 C983F5_F5_SOUTHEAST_G6; bottom_bar C983AB_BOTTOM_BAR;     *)
(* f5_left_full_bar C983LO_F5_LEFT_FULL_BAR; f5_top_only_points              *)
(* C983F5TOP_F5_TOP_ONLY_POINTS; f5_final_central C983F5RF_F5_FINAL_CENTRAL; *)
(* auxiliary_inside / missing_auxiliary via OO_AUX_EXACT (c983f4f_point,     *)
(* c983fnf_missing).  The existential square E is stated with its OpenSquare *)
(* invariants (unit normal, positive side).  Tag C983FNF_.                   *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_LeftOrigin.ml";;
needs "n12/geometry/CP_OtherCases_C983_MergedCenterF5.ml";;
needs "n12/geometry/CP_OtherCases_PositiveEnding.ml";;
needs "n12/geometry/CP_OtherCases_InwardSign.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* Lean: southeast_inward_check (private) *)
let C983FNF_SOUTHEAST_INWARD_CHECK = prove
 (`forall s. MEM s c983f5rf_final_southeast ==> ~(8 IN s) ==> 4 IN s`,
  c983f5_check [c983f5rf_final_southeast]);;

(* |- ~(j IN actual i)  to  |- ~linside (owner i) x_j y_j *)
let c983fnf_missing th =
  let th1 = CONV_RULE C983F4F_ACT_CONV th in
  let mem = rand (concl th1) in
  let j = dest_small_numeral (lhand mem) and m = rand (rand mem) in
  let eq = SPECL (C983E_VARS @ [m]) (oo_aux_point j) in
  CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (EQ_MP (SYM (AP_TERM `~` eq)) th1);;

let c983fnf_tr t = match t with
    [c; s; u; v; a] ->
      let mul x y = mk_binop `( * ):real->real->real` x y
      and add x y = mk_binop `(+):real->real->real` x y
      and sub x y = mk_binop `(-):real->real->real` x y in
      [c; s; sub u (add (mul c `&2`) (mul s `&2`));
       sub v (add (mul (mk_comb(`(--):real->real`, s)) `&2`) (mul c `&2`)); a]
  | _ -> failwith "c983fnf_tr";;

let C983FNF_E = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;

(* Lean: f5_negative_frame *)
let C983FNF_F5_NEGATIVE_FRAME =
  let f5tm = c983f4f_mem 5 7 in
  let inE x y = list_mk_comb(`linside`, C983FNF_E @ [x; y]) in
  let xv = `x:real` and yv = `y:real` in
  let plus2 t = mk_binop `(+):real->real->real` t `&2` in
  let concl = list_mk_exists(C983FNF_E, list_mk_conj
    [`cE * cE + sE * sE = &1`; `&0 < aE`; `&0 < cE`; `sE < &0`; `--sE <= cE`; `aE:real = l`;
     list_mk_forall([xv; yv], mk_iff(inE xv yv, c983ab_in 512 (plus2 xv) (plus2 yv)))]) in
  prove
   (c983sa_stmt [f5tm] concl,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
    let f5 = ASSUME f5tm in
    let tT = c983fnf_tr (c983ab_own 512) and tW = c983fnf_tr (c983ab_own 2304) in
    let iffT = ASSUME (list_mk_forall([xv; yv],
                 mk_iff(inE xv yv, list_mk_comb(`linside`, tT @ [xv; yv])))) in
    let iffE = REWRITE_RULE[CCIP_INSIDE_TRANSLATED] iffT in
    let rr = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) in
    let toE th x y = EQ_MP (SYM (rr (SPECL [x; y] iffE))) th in
    let notE th x y = EQ_MP (SYM (AP_TERM `~` (rr (SPECL [x; y] iffE)))) th in
    let wconv = REWRITE_CONV[CCIP_INSIDE_TRANSLATED] THENC ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV in
    let toW th x y =
      let tm = list_mk_comb(`linside`, tW @ [x; y]) in EQ_MP (SYM (wconv tm)) th in
    let west = toW (seed 7 `&33 / &20` `&33 / &20`) `--(&7 / &20)` `--(&7 / &20)` in
    let center = toW (c983f5_use C983MCF_F5_MERGED_CENTER [f5]) `&0` `&0` in
    let upperInward = toW (c983f4f_point f5) `&0` `&13 / &50` in
    let marker = toE (seed 5 `&47 / &20` `&33 / &20`) `&7 / &20` `--(&7 / &20)` in
    let elbow = toE (c983f4f_point (c983f5_use C983F5_F5_SOUTHEAST_G6 [f5])) `&13 / &50` `&0` in
    let hh = c983f4f_hh () in
    let fnfBottomBar = REWRITE_RULE[IMP_IMP] (MP (SPECL C983E_VARS C983AB_BOTTOM_BAR) hh) in
    let fnfLeftBar = REWRITE_RULE[IMP_IMP] (c983f5_use C983LO_F5_LEFT_FULL_BAR [f5]) in
    let a512_8192 = apart 512 8192 and a2304_4096 = apart 2304 4096 and a2304_512 = apart 2304 512 in
    let capth = MP (SPECL C983E_VARS OO_SIDE_LE) (ASSUME C983F4F_NP) in
    MP_TAC(SPECL tT CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [MP_TAC (unit 512) THEN CONV_TAC REAL_RING; ACCEPT_TAC pos];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC C983FNF_E THEN STRIP_TAC THEN
    SUBGOAL_THEN `forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside cE sE uE vE aE x (--(&1))` ASSUME_TAC THENL
     [X_GEN_TAC `x:real` THEN DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[iffE] THEN DISCH_TAC THEN
      SUBGOAL_THEN (c983ab_in 8192 `&2 + x` `&2 + --(&1)`) ASSUME_TAC THENL
       [CONV_TAC(RAND_CONV REAL_RAT_REDUCE_CONV) THEN MATCH_MP_TAC fnfBottomBar THEN RASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`&2 + x`; `&2 + --(&1)`] a512_8192) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (mk_forall(`y:real`, mk_imp(`&0 <= y`, mk_imp(`y <= &4 / &5`,
                    mk_neg(list_mk_comb(`linside`, tW @ [`--(&1)`; `y:real`])))))) ASSUME_TAC THENL
     [X_GEN_TAC `y:real` THEN DISCH_TAC THEN DISCH_TAC THEN REWRITE_TAC[CCIP_INSIDE_TRANSLATED] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN (c983ab_in 4096 `&2 + --(&1)` `&2 + y`) ASSUME_TAC THENL
       [CONV_TAC(RATOR_CONV(RAND_CONV REAL_RAT_REDUCE_CONV)) THEN MATCH_MP_TAC fnfLeftBar THEN RASM_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPECL [`&2 + --(&1)`; `&2 + y`] a2304_4096) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN (list_mk_comb(`ldisj`, tW @ C983FNF_E)) ASSUME_TAC THENL
     [REWRITE_TAC[ldisj; iffE; CCIP_INSIDE_TRANSLATED] THEN REPEAT GEN_TAC THEN
      MATCH_ACCEPT_TAC a2304_512;
      ALL_TAC] THEN
    MAP_EVERY ASSUME_TAC [west; center; upperInward; marker; elbow; capth; side; pos; unit 2304] THEN
    SUBGOAL_THEN `&1 < aE` ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN (mk_eq(`l:real`, `aE:real`)) ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `sE < &0` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= sE /\ sE <= cE` STRIP_ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
      ASM_CASES_TAC (c983f4f_mem 8 5) THENL
       [(let f8 = ASSUME (c983f4f_mem 8 5) in
        let points = c983f5_use C983F5TOP_F5_TOP_ONLY_POINTS [f5] in
        let outer = toE (c983f4f_point f8) `&1` `--(&13 / &50)` in
        let missingOrigin = notE (excl 512 16384 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 points)))) `&1` `&0` in
        let missingSharp = notE (excl 512 1024 (CONJUNCT1 points)) `&21 / &40` `&1 / &8` in
        MP_TAC(SPECL (tW @ C983FNF_E) OCPEND_NONNEGATIVE_IMPOSSIBLE) THEN
        MAP_EVERY ASSUME_TAC [outer; missingOrigin; missingSharp] THEN
        REWRITE_TAC[TAUT `(p ==> false) ==> false <=> p`] THEN REPEAT CONJ_TAC THEN
        FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC]);
        (let nf8 = ASSUME (mk_neg (c983f4f_mem 8 5)) in
        let se = CONJUNCT1 (c983f5_use C983F5RF_F5_FINAL_CENTRAL [f5]) in
        let f4 = MP (MATCH_MP C983FNF_SOUTHEAST_INWARD_CHECK
                       se) nf8 in
        let inner = toE (c983f4f_point f4) `&0` `--(&13 / &50)` in
        let missingF = notE (c983fnf_missing nf8) `&1` `--(&13 / &50)` in
        MP_TAC(SPECL (tW @ C983FNF_E) OCISG_POSITIVE_IMPOSSIBLE) THEN
        MAP_EVERY ASSUME_TAC [inner; missingF] THEN
        REWRITE_TAC[TAUT `(p ==> false) ==> false <=> p`] THEN REPEAT CONJ_TAC THEN
        FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC])];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC C983FNF_E THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           REPEAT GEN_TAC THEN REWRITE_TAC[iffE] THEN REWRITE_TAC[REAL_ADD_SYM] THEN NO_TAC;
           RASM_ARITH_TAC]);;

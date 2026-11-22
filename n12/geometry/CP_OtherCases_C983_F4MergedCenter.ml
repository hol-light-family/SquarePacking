(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4MergedCenter.lean            *)
(* (N12Compact.Completion.OtherCases.C983.F4MergedCenter).  Sections 1-3 of  *)
(* C983-F4-MERGED-CENTER.md; coordinates of Input translated by (-2,-2).     *)
(* Input W K is c983fmc_input (W) (K) over two 5-tuples; for the generic     *)
(* lemmas the OpenSquare invariants (unit normal, positive side) of W and K  *)
(* are explicit hypotheses.  Conventions of CP_OtherCases_C983_LeftOrigin.ml:*)
(* owners p 0 / 1 / 7 / 8 = owner 1 / 2 / 2304 / 4096; q.translated 2 2 is   *)
(* (c, s, u - (c * &2 + s * &2), v - (--s * &2 + c * &2), a)                  *)
(* (CCIP_INSIDE_TRANSLATED).  owners_cap = OO_SIDE_LE, merged_g3 =           *)
(* C983F4F_MERGED_G3, auxiliary_inside = c983f4f_point; WallProfile.vertex / *)
(* strict_closed_segment / vertical_owned = OCWPVG_*; ABTransverse upper /   *)
(* lower / strict_bounds = ABT_upper / ABT_lower / ABT_STRICT_BOUNDS.        *)
(* angle_window's `let z := s/(1+c)` is substituted.  Tag C983FMC_.          *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_MergedCenterF5.ml";;
needs "n12/geometry/CP_OtherCases_C983_LeftOrigin.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/ABTransverse.ml";;

(* Lean: Input *)
let c983fmc_input = new_definition
 `c983fmc_input (cW:real) (sW:real) (uW:real) (vW:real) (aW:real)
                (cK:real) (sK:real) (uK:real) (vK:real) (aK:real) <=>
    &1 < aW /\ aW <= &1001 / &1000 /\ aW = aK /\
    linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
    linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
    linside cW sW uW vW aW (&0) (--(&13 / &50)) /\
    linside cW sW uW vW aW (--(&13 / &50)) (&0) /\
    linside cK sK uK vK aK (--(&1)) (--(&1)) /\
    linside cK sK uK vK aK (--(&1)) (--(&13 / &50)) /\
    linside cK sK uK vK aK (--(&31 / &25)) (--(&13 / &100)) /\
    linside cK sK uK vK aK (--(&543 / &500)) (--(&1)) /\
    ~linside cW sW uW vW aW (--(&1)) (&0) /\
    ~linside cK sK uK vK aK (--(&1)) (--(&543 / &500)) /\
    (forall x y. linside cK sK uK vK aK x y ==> --(&2) <= x) /\
    ldisj cK sK uK vK aK cW sW uW vW aW`;;

let C983FMC_W = [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`];;
let C983FMC_K = [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`];;
let C983FMC_HYP =
  "cW * cW + sW * sW = &1 /\\ &0 < aW /\\ cK * cK + sK * sK = &1 /\\ &0 < aK /\\ c983fmc_input cW sW uW vW aW cK sK uK vK aK";;
let c983fmc_stmtv vars extra concl = parse_term (Printf.sprintf "!cW sW uW vW aW cK sK uK vK aK%s. %s ==> %s"
  vars (String.concat " /\\ " (C983FMC_HYP :: extra)) concl);;
let c983fmc_stmt = c983fmc_stmtv "";;
let C983FMC_ORIENT = ["&0 < cW"; "&0 <= sW"; "sW <= cW"; "~linside cW sW uW vW aW (&0) (&0)"];;

(* open the hypotheses, keeping the Input assumption *)
let C983FMC_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if is_comb (concl th) && fst (strip_comb (concl th)) = `c983fmc_input`
                        then STRIP_ASSUME_TAC (REWRITE_RULE[c983fmc_input] th) else NO_TAC);;
(* unfold the positive linside assumptions *)
let C983FMC_UNFOLD_TAC =
  RULE_ASSUM_TAC(fun th -> let t = concl th in
    if is_comb t && fst (strip_comb t) = `linside` then REWRITE_RULE[linside] th else th);;
let C983FMC_LIN = NLIN_TAC ~deg2:false [];;
let C983FMC_FACT t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;
let C983FMC_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside; TAUT `~p ==> false <=> p`] THEN
  REPEAT CONJ_TAC THEN C983FMC_LIN;;

(* use a generic lemma whose hypotheses are all in the assumptions *)
let C983FMC_USE th =
  MP_TAC(SPECL (C983FMC_W @ C983FMC_K) th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC];;

(* translated 2 2 of a 5-tuple *)
let c983fmc_tr t = match t with
    [c; s; u; v; a] ->
      let mul x y = mk_binop `( * ):real->real->real` x y
      and add x y = mk_binop `(+):real->real->real` x y
      and sub x y = mk_binop `(-):real->real->real` x y in
      [c; s; sub u (add (mul c `&2`) (mul s `&2`));
       sub v (add (mul (mk_comb(`(--):real->real`, s)) `&2`) (mul c `&2`)); a]
  | _ -> failwith "c983fmc_tr";;

(* Lean: actual_input *)
let C983FMC_ACTUAL_INPUT =
  let f4tm = c983f4f_mem 4 7 and corner = c983ab_in 2 `&1` `&1` in
  prove
   (c983sa_stmt [f4tm; corner]
      (list_mk_comb(`c983fmc_input`, c983fmc_tr (c983ab_own 2304) @ c983fmc_tr (c983ab_own 2))),
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
    let f4 = ASSUME f4tm in
    let f3 = CONJUNCT1 (c983lo_use C983F4F_F4_TOP [f4]) in
    let g7 = c983lo_use C983F4CE_F4_NORTHEAST_G7 [f4] in
    let left = c983lo_use C983LO_LEFT_ORIGIN_OF_TOP_G7 [f3; g7] in
    let facts = [side; MP (SPECL C983E_VARS OO_SIDE_LE) (ASSUME C983F4F_NP);
                 seed 7 `&33 / &20` `&33 / &20`; seed 7 `&33 / &20` `&47 / &20`;
                 c983f4f_point f4; c983f4f_point (c983lo_use C983F4F_MERGED_G3 []);
                 seed 1 `&1` `&87 / &50`; seed 1 `&19 / &25` `&187 / &100`;
                 seed 1 `&457 / &500` `&1`;
                 excl 2304 4096 left; excl 2 1 (seed 0 `&1` `&457 / &500`);
                 apart 2 2304] in
    let bx = REWRITE_RULE[lcont] (box 2) in
    REWRITE_TAC[c983fmc_input; ldisj; CCIP_INSIDE_TRANSLATED] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC; REFL_TAC; REPEAT GEN_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
           REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP bx) THEN REAL_ARITH_TAC]);;

(* Lean: missing_faces *)
let C983FMC_MISSING_FACES = prove
 (c983fmc_stmt C983FMC_ORIENT
    "uW + aW <= &0 /\\ uW < --(&1) /\\ vW + aW <= sW /\\ (&7 / &13) * cW < sW",
  C983FMC_OPEN_TAC THEN C983FMC_UNFOLD_TAC THEN
  C983FMC_FACT `cW <= &1` (NLIN_TAC [SQ_NONNEG `sW:real`]) THEN
  C983FMC_FACT `uW + aW <= &0`
    (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C983FMC_MISS_TAC `~linside cW sW uW vW aW (&0) (&0)`) THEN
  C983FMC_FACT `uW < --(&1)` C983FMC_LIN THEN
  C983FMC_FACT `vW + aW <= sW`
    (REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
     C983FMC_MISS_TAC `~linside cW sW uW vW aW (--(&1)) (&0)`) THEN
  ASM_REWRITE_TAC[] THEN C983FMC_LIN);;

(* Lean: singleton_bar *)
let C983FMC_SINGLETON_BAR = prove
 (c983fmc_stmt [] "!y. --(&1) <= y ==> y <= --(&13 / &50) ==> linside cK sK uK vK aK (--(&1)) y",
  C983FMC_OPEN_TAC THEN MATCH_MP_TAC OCWPVG_VERTICAL_OWNED THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: no_left_vertex *)
let C983FMC_NO_LEFT_VERTEX = prove
 (c983fmc_stmtv " x y" ["lclosed cW sW uW vW aW x y"; "x < --(&1)"; "--(&1) < y"; "y < --(&13 / &50)"] "F",
  C983FMC_OPEN_TAC THEN
  SUBGOAL_THEN `&0 < --(&7 / &20) - x` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `exists t. &0 < t /\ t < &1 /\ t * (--(&7 / &20) - x) = --(&1) - x` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(--(&1) - x) / (--(&7 / &20) - x)` THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL (C983FMC_W @ [`x:real`; `y:real`; `--(&7 / &20)`; `--(&7 / &20)`; `t:real`])
    OCWPVG_STRICT_CLOSED_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&1 - t) * x + t * --(&7 / &20) = --(&1)` SUBST1_TAC THENL
   [UNDISCH_TAC `t * (--(&7 / &20) - x) = --(&1) - x` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 < (&1 - t) * (y + &1) /\ &0 < (&1 - t) * (--(&13 / &50) - y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (C983FMC_W @ C983FMC_K) C983FMC_SINGLETON_BAR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(&1 - t) * y + t * --(&7 / &20)`) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`--(&1)`; `(&1 - t) * y + t * --(&7 / &20)`] o
    REWRITE_RULE[ldisj] o check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `ldisj`)) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: auxiliary_not_upper *)
let C983FMC_AUXILIARY_NOT_UPPER = prove
 (c983fmc_stmt (C983FMC_ORIENT @ ["vW + aW <= sW - (&13 / &50) * cW"]) "F",
  C983FMC_OPEN_TAC THEN C983FMC_USE C983FMC_MISSING_FACES THEN
  SUBGOAL_THEN `lclosed cW sW uW vW aW (cW * uW - sW * (vW + aW)) (sW * uW + cW * (vW + aW))` ASSUME_TAC THENL
   [MATCH_MP_TAC OCWPVG_VERTEX THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  C983FMC_UNFOLD_TAC THEN
  C983FMC_FACT `(&61 / &65) * cW < sW` C983FMC_LIN THEN
  C983FMC_FACT `cW <= &1` (NLIN_TAC [SQ_NONNEG `sW:real`]) THEN
  C983FMC_FACT `sW * sW <= cW * cW`
    (MATCH_MP_TAC REAL_LE_MUL2 THEN RASM_ARITH_TAC) THEN
  C983FMC_FACT `&7 / &10 < cW` (NLIN_TAC []) THEN
  C983FMC_FACT `&13 / &20 < sW` C983FMC_LIN THEN
  C983FMC_FACT `&27 / &20 < cW + sW` C983FMC_LIN THEN
  C983FMC_FACT `sW * sW <= &1 / &2` C983FMC_LIN THEN
  C983FMC_FACT `&1 / &2 <= cW * cW` C983FMC_LIN THEN
  C983FMC_FACT `sW < &5 / &7` (NLIN_TAC []) THEN
  C983FMC_FACT `(&7 / &20) * (cW + sW) < vW + aW` C983FMC_LIN THEN
  MATCH_MP_TAC (SPECL (C983FMC_W @ C983FMC_K @ [`cW * uW - sW * (vW + aW)`; `sW * uW + cW * (vW + aW)`])
    C983FMC_NO_LEFT_VERTEX) THEN
  REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THENL
   [(* xLeft *)
    C983FMC_FACT `&0 < cW * (--(&1) - uW)` (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_FACT `&0 < sW * ((vW + aW) - (&7 / &20) * (cW + sW))`
      (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_FACT `&0 < (sW - &13 / &20) * (cW + sW)` (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_LIN;
    (* yLow *)
    C983FMC_FACT `&0 < sW * (uW + (&13 / &50) * sW + aW)` (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_FACT `&0 < cW * ((vW + aW) - (&7 / &20) * (cW + sW))`
      (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_FACT `&0 <= sW * (&1001 / &1000 - aW)` (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_FACT `&0 <= cW * sW` (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_LIN;
    (* yHigh *)
    C983FMC_FACT `&0 < sW * (--(&1) - uW)` (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_FACT `&0 <= cW * (sW - (&13 / &50) * cW - (vW + aW))`
      (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
    C983FMC_FACT `&0 < (sW * sW) * (sW - (&13 / &50) * (&1 + cW))`
      (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
        [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; RASM_ARITH_TAC]) THEN
    C983FMC_FACT `(&1 + cW) * (sW * (&1 - cW) - (&13 / &50) * (sW * sW)) =
                  (sW * sW) * (sW - (&13 / &50) * (&1 + cW))`
      (UNDISCH_TAC `cW * cW + sW * sW = &1` THEN CONV_TAC REAL_RING) THEN
    C983FMC_FACT `&0 < sW * (&1 - cW) - (&13 / &50) * (sW * sW)`
      (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
       SUBGOAL_THEN `(&1 + cW) * (sW * (&1 - cW) - (&13 / &50) * (sW * sW)) <= &0` MP_TAC THENL
        [REWRITE_TAC[REAL_ARITH `x * y <= &0 <=> &0 <= x * --y`] THEN
         MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC;
         ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]) THEN
    C983FMC_LIN]);;

(* Lean: auxiliary_lower *)
let C983FMC_AUXILIARY_LOWER = prove
 (c983fmc_stmt C983FMC_ORIENT "--cW - (&13 / &50) * sW <= uW /\\ &1 < cW + (&13 / &50) * sW",
  C983FMC_OPEN_TAC THEN C983FMC_USE C983FMC_MISSING_FACES THEN
  SUBGOAL_THEN `~linside cW sW uW vW aW (--(&1)) (--(&13 / &50))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`--(&1)`; `--(&13 / &50)`] o
      REWRITE_RULE[ldisj] o check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `ldisj`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `--cW - (&13 / &50) * sW <= uW` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC (SPECL (C983FMC_W @ C983FMC_K) C983FMC_AUXILIARY_NOT_UPPER) THEN
    REPEAT CONJ_TAC THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983FMC_UNFOLD_TAC THEN
    C983FMC_MISS_TAC `~linside cW sW uW vW aW (--(&1)) (--(&13 / &50))`;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

(* Lean: separator_cone *)
let C983FMC_SEPARATOR_CONE = prove
 (c983fmc_stmtv " nx ny" ["nx pow 2 + ny pow 2 = &1";
                "ABT_upper cK sK uK vK aK nx ny <= ABT_lower cW sW uW vW aW nx ny"]
    "&0 < nx /\\ &0 < nx + ny",
  C983FMC_OPEN_TAC THEN
  let sb t x y = MP_TAC(SPECL (t @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
                 ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] in
  sb C983FMC_K `--(&1)` `--(&13 / &50)` THEN sb C983FMC_W `&0` `--(&13 / &50)` THEN
  sb C983FMC_K `--(&1)` `--(&1)` THEN sb C983FMC_W `--(&7 / &20)` `--(&7 / &20)` THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: angle_window *)
let C983FMC_ANGLE_WINDOW = prove
 (c983fmc_stmt C983FMC_ORIENT
   "&1 / &4 < sW / (&1 + cW) /\\ sW / (&1 + cW) < &13 / &50 /\\
    sW * (sW / (&1 + cW)) = &1 - cW /\\
    &87 / &100 < cW /\\ &47 / &100 < sW /\\ sW < &49 / &100 /\\
    &27 / &20 < cW + sW /\\ &19 / &50 < cW - sW",
  C983FMC_OPEN_TAC THEN C983FMC_USE C983FMC_MISSING_FACES THEN
  C983FMC_USE C983FMC_AUXILIARY_LOWER THEN
  ABBREV_TAC `z = sW / (&1 + cW)` THEN
  C983FMC_FACT `&0 < sW` RASM_ARITH_TAC THEN
  C983FMC_FACT `&0 < &1 + cW` RASM_ARITH_TAC THEN
  C983FMC_FACT `z * (&1 + cW) = sW`
    (EXPAND_TAC "z" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN RASM_ARITH_TAC) THEN
  C983FMC_FACT `&0 < z` (NLIN_TAC []) THEN
  C983FMC_FACT `sW * z = &1 - cW`
    (SUBGOAL_THEN `(&1 + cW) * (sW * z - (&1 - cW)) = &0` MP_TAC THENL
      [UNDISCH_TAC `z * (&1 + cW) = sW` THEN UNDISCH_TAC `cW * cW + sW * sW = &1` THEN
       CONV_TAC REAL_RING;
       REWRITE_TAC[REAL_ENTIRE] THEN STRIP_TAC THENL [RASM_ARITH_TAC; RASM_ARITH_TAC]]) THEN
  C983FMC_FACT `cW * (&1 + z * z) = &1 - z * z`
    (UNDISCH_TAC `z * (&1 + cW) = sW` THEN UNDISCH_TAC `sW * z = &1 - cW` THEN CONV_TAC REAL_RING) THEN
  C983FMC_FACT `sW * (&1 + z * z) = &2 * z`
    (UNDISCH_TAC `z * (&1 + cW) = sW` THEN UNDISCH_TAC `sW * z = &1 - cW` THEN CONV_TAC REAL_RING) THEN
  C983FMC_FACT `&1 / &4 < z`
    (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
     C983FMC_FACT `z * z <= &1 / &16` (NLIN_TAC []) THEN
     C983FMC_FACT `&0 < (&13 * sW - &7 * cW) * (&1 + z * z)`
       (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
         [RASM_ARITH_TAC; MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC]) THEN
     C983FMC_LIN) THEN
  C983FMC_FACT `z < &13 / &50`
    (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
     C983FMC_FACT `&0 <= sW * (z - &13 / &50)` (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
     C983FMC_LIN) THEN
  C983FMC_FACT `z * z < &169 / &2500` (NLIN_TAC []) THEN
  C983FMC_FACT `&2331 / &2669 < cW`
    (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
     C983FMC_FACT `&0 <= (&1 + z * z) * (&2331 / &2669 - cW)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
         [MP_TAC(SPEC `z:real` REAL_LE_SQUARE) THEN REAL_ARITH_TAC; RASM_ARITH_TAC]) THEN
     C983FMC_LIN) THEN
  C983FMC_FACT `&47 / &100 < sW`
    (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
     C983FMC_FACT `&0 < (&1 + cW) * (z - &1 / &4)` (MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
     C983FMC_FACT `cW < &22 / &25` C983FMC_LIN THEN
     C983FMC_FACT `cW * cW < &484 / &625` (NLIN_TAC []) THEN
     C983FMC_FACT `sW * sW <= &2209 / &10000` (NLIN_TAC []) THEN
     C983FMC_LIN) THEN
  C983FMC_FACT `(&2331 / &2669) * (&2331 / &2669) < cW * cW` (NLIN_TAC []) THEN
  C983FMC_FACT `sW < &49 / &100` (NLIN_TAC []) THEN
  C983FMC_FACT `&27 / &20 < cW + sW`
    (REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
     C983FMC_FACT `&0 <= (&27 / &20 - sW - cW) * (&27 / &20 - sW + cW)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
     C983FMC_FACT `&0 <= (sW - &47 / &100) * (&49 / &100 - sW)`
       (MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN C983FMC_LIN) THEN
     C983FMC_LIN) THEN
  ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC);;

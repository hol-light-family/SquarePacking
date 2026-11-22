(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/TopOriginSign.lean                  *)
(* (N12Compact.C1092MMMPTopOriginSign).  Actual-owner reduction of the       *)
(* missing MMMP top origin to the strictly negative canonical left-wall      *)
(* sign.  Conventions of CP_C1092_MMMP_Origins.ml / CP_C1092_MMMP_LeftFar.ml *)
(* (owners p i at mask EL i c1092wc_code, side l; charts via c1092mo_layers).*)
(* WallProfile.boundary_origin via c1092mo_origin; C981CompletionTopReach.   *)
(* origin_alternative C981TR_ORIGIN_ALTERNATIVE; centered_frame              *)
(* C1092MWC_CENTERED_FRAME; left_origin C1092MO_LEFT_ORIGIN; LeftFar.point   *)
(* C1092MLF_POINT; top_origin_of_left_halfpoint                              *)
(* C1092MAP_TOP_ORIGIN_OF_LEFT_HALFPOINT; northwest_left                     *)
(* C1092MO_NORTHWEST_LEFT; LeftCenterFaces.positive / negative               *)
(* C1092MLCF_POSITIVE / NEGATIVE; CenterCorner.impossible                    *)
(* C1092MMCC_IMPOSSIBLE; Normal is c977cc_normal.  The structure             *)
(* NegativeLeft p L is c1092mtos_negleft (packing) (L); the OpenSquare       *)
(* invariants of L (unit normal, positive side) are stated explicitly in the *)
(* existential.  Tag C1092MTOS_.                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MMMP_CenterCorner.ml";;
needs "n12/geometry/CP_C1092_MMMP_ActualProfile.ml";;
needs "n12/geometry/CP_C1092_MMMP_LeftFar.ml";;
needs "n12/geometry/CP_C981_TopReach.ml";;

let C1092MTOS_MISSING = "~" ^ c1092mmpe_in 11 "&2" "&3";;

(* Lean: corner_halfpoint *)
let C1092MTOS_CORNER_HALFPOINT = prove
 (c1092map_stmt [C1092MTOS_MISSING] (c1092mmpe_in 3 "&1" "&5 / &2"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
  let top = c1092mo_use C1092MMPE_TOP_PAIR in
  let th = c1092mo_origin [C1092MO_Y] 11 3 `&457 / &500` `&8 / &5`
    [c1092mo_seed 11 (`&2`, `&1543 / &500`); CONJUNCT1 top;
     c1092mo_seed 3 (`&1`, `&1543 / &500`); c1092mo_seed 3 (`&1`, `&3`);
     ASSUME (mk_neg (c1092mo_in 3 `&1` `&5 / &2`))]
    [`x:real`; `&4 - y`] in
  UNDISCH_TAC (mk_neg (c1092mo_in 11 `&2` `&3`)) THEN REWRITE_TAC[th]);;

(* Lean: top_alternative *)
let C1092MTOS_TOP_ALTERNATIVE = prove
 (c1092map_stmt [C1092MTOS_MISSING] (c1092mmpe_in 11 "&6 / &5" "&3"),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let t, eqs = c1092mo_layers 11 [C1092MO_X; c1092mo_tr `&2` `&3`] in
  let top = c1092mo_use C1092MMPE_TOP_PAIR in
  let box = REWRITE_RULE[lcont] (c1092mo_box 11) in
  let facts = [c1092mo_punit 11 t; c1092mo_pos (); c1092mo_side ();
               c1092mo_seed 11 (`&2`, `&1543 / &500`); CONJUNCT1 top;
               ASSUME (mk_neg (c1092mo_in 11 `&2` `&3`))] in
  MP_TAC(SPECL t C981TR_ORIGIN_ALTERNATIVE) THEN CONV_TAC (c1092mo_conv eqs) THEN
  ANTS_TAC THENL
   [MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP box) THEN REAL_ARITH_TAC];
    SIMP_TAC[]]);;

(* Lean: NegativeLeft *)
let c1092mtos_negleft = new_definition (parse_term (Printf.sprintf
  "c1092mtos_negleft (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
     (cL:real) (sL:real) (uL:real) (vL:real) (aL:real) <=>
     aL = l /\\ (!x y. linside cL sL uL vL aL x y <=> %s) /\\
     c977cc_normal cL (--sL) /\\ sL < &0 /\\ &0 <= lcy cL sL uL vL aL /\\
     lcx cL sL uL vL aL < &0 /\\ vL + aL <= cL / &2"
  (c1092mmpe_in 8 "&1 + x" "&2 + y")));;

let C1092MTOS_CLOSE_TAC = REPEAT CONJ_TAC THEN FIRST [FIRST_ASSUM ACCEPT_TAC; RASM_ARITH_TAC];;

(* Lean: negative_left_of_missing_top *)
let C1092MTOS_NEGATIVE_LEFT_OF_MISSING_TOP = prove
 (c1092map_stmt [C1092MTOS_MISSING]
    "?cL sL uL vL aL. cL * cL + sL * sL = &1 /\\ &0 < aL /\\ c1092mtos_negleft c1 c2 a b l cL sL uL vL aL",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (parse_term ("~" ^ c1092mmpe_in 8 "&1" "&5 / &2")) ASSUME_TAC THENL
   [DISCH_TAC THEN MP_TAC(SPEC_ALL C1092MAP_TOP_ORIGIN_OF_LEFT_HALFPOINT) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL C1092MTOS_CORNER_HALFPOINT) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092MTOS_TOP_ALTERNATIVE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[c1092mtos_negleft] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let tW, eqW = c1092mo_layers 8 [c1092mo_tr `&1` `&2`] in
  let tK, eqK = c1092mo_layers 3 [c1092mo_tr `&1` `&2`] in
  let tL = [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`] in
  let inL x y = list_mk_comb(`linside`, tL @ [x; y]) in
  let xv = `x:real` and yv = `y:real` in
  let iffW = ASSUME (mk_forall(xv, mk_forall(yv,
               mk_iff(inL xv yv, list_mk_comb(`linside`, tW @ [xv; yv]))))) in
  let iff = REWRITE_RULE eqW iffW in
  let rr = CONV_RULE (RAND_CONV (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) in
  let toL th x y = EQ_MP (SYM (rr (SPECL [x; y] iff))) th in
  let notL th x y = EQ_MP (SYM (AP_TERM `~` (rr (SPECL [x; y] iff)))) th in
  let a i x y = ASSUME (c1092mo_in i x y) in
  let left = c1092mo_use C1092MO_LEFT_ORIGIN and far = c1092mo_use C1092MLF_POINT in
  let cut = CONV_RULE C1092MO_CODE_CONV (UNDISCH (SPECL C1092MMPE_V C1092MPC_CUT)) in
  let thO = toL left `&0` `&0` and thG = toL far `&0` `&2 / &5` in
  let thT = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)
    (MATCH_MP C1092WC_INSIDE_SEGMENT (end_itlist CONJ [thO; thG;
       REAL_ARITH `&0 <= &39 / &40`; REAL_ARITH `&39 / &40 <= &1`])) in
  let thH = notL (ASSUME (mk_neg (c1092mo_in 8 `&1` `&5 / &2`))) `&0` `&1 / &2` in
  let thX = notL (c1092mo_excl 8 7 (c1092mo_use C1092MO_NORTHWEST_LEFT)) `&1 / &2` `&0` in
  let apart83 = c1092mo_apart 8 3 in
  MP_TAC(SPECL tW C1092MWC_CENTERED_FRAME) THEN
  ANTS_TAC THENL [REWRITE_TAC[c1092mo_punit 8 tW; c1092mo_pos ()]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC tL THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 < aL` ASSUME_TAC THENL
   [MP_TAC(c1092mo_side ()) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= lcy cL sL uL vL aL` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq (concl th) && is_comb (lhs (concl th)) &&
        fst (strip_comb (lhs (concl th))) = `lcy` then REWRITE_TAC[th] else NO_TAC) THEN
    MP_TAC cut THEN MP_TAC (c1092mo_unit 8) THEN REWRITE_TAC[lcy] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY ASSUME_TAC [thO; thG; thT; thH; thX] THEN
  SUBGOAL_THEN `sL < &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `c977cc_normal cL sL` ASSUME_TAC THENL
     [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL tL C1092MLCF_POSITIVE) THEN
    ANTS_TAC THENL [C1092MTOS_CLOSE_TAC; STRIP_TAC] THEN
    MATCH_MP_TAC (SPECL (tL @ tK) C1092MMCC_IMPOSSIBLE) THEN
    REWRITE_TAC[ldisj; iff] THEN CONV_TAC (c1092mo_conv eqK) THEN
    MAP_EVERY ASSUME_TAC [c1092mo_punit 3 tK; c1092mo_pos (); c1092mo_seed 3 (`&1`, `&3`);
      c1092mo_excl 3 11 (a 11 `&6 / &5` `&3`); a 3 `&1` `&5 / &2`; far] THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           REPEAT GEN_TAC THEN MATCH_ACCEPT_TAC apart83;
           RASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cL (--sL)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL tL C1092MLCF_NEGATIVE) THEN
  ANTS_TAC THENL [C1092MTOS_CLOSE_TAC; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC tL THEN REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC; ACCEPT_TAC iff; RASM_ARITH_TAC]);;

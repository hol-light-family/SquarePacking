(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975IncomingCut.lean.             *)
(* Genuine C975 reductions after the complete original entrance.  owner p m  *)
(* is the 5-tuple (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l; auxiliaries *)
(* p m is ooaux c1 c2 a b l m; natAuxOwners p 1 (ownerIndex p m) is          *)
(* auxown 1 (c1 (oidx ..)) .. l.  Private helpers: aux_inside = oo_aux_point *)
(* (c975ic_aux at compulsory points), foreign = C975IC_FOREIGN_TAC (OO_APART *)
(* at a point), seed_point = oo_seed, g_combined = C975E_G_COMBINED,         *)
(* top_g_checked = C975IC_TOP_G_CHECKED.  C975Entrance.compulsory /          *)
(* top_alternatives: C975E_COMPULSORY / C975E_TOP_ALTERNATIVES;              *)
(* TopMergedInward.short_impossible: FCTMI_SHORT_IMPOSSIBLE; TopPairPoint.   *)
(* point: FCTPP_POINT; WallHighFromMarker.point: FCWHM_POINT;                *)
(* C981CompletionCrosspoint.point: C981CP_POINT; C975Domains.topG:           *)
(* C975D_TOPG (via HDOM_OWNER).  The checked TriangleCertificate of          *)
(* not_top_elbow is replaced by the convex combination it certifies (linear  *)
(* arithmetic on the face inequalities).  Tag C975IC_.                       *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975Entrance.ml";;
needs "n12/geometry/CP_FiniteCases_TopMergedInward.ml";;
needs "n12/geometry/CP_FiniteCases_TopPairPoint.ml";;
needs "n12/geometry/CP_FiniteCases_WallHighFromMarker.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;

let C975IC_V5 = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

let c975ic_stmt hyps concl =
  list_mk_forall(C975IC_V5,
    mk_imp(list_mk_conj([`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = c975d_family`] @ hyps),
           concl));;

let c975ic_owner m = map (fun f -> list_mk_comb(f, C975IC_V5 @ [mk_small_numeral m]))
  [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let c975ic_own m x y = list_mk_comb(`linside`, c975ic_owner m @ [x; y]);;
let c975ic_mem j m = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j),
                             list_mk_comb(`ooaux`, C975IC_V5 @ [mk_small_numeral m]));;

let c975ic_seed m p = oo_inst C975D_F (oo_seed m p);;

(* Lean: aux_inside (private), at the non-disjunctive compulsory points *)
let c975ic_aux m j =
  let th = SPECL (C975IC_V5 @ [mk_small_numeral m]) (oo_aux_point j) in
  prove(c975ic_stmt [] (lhs (concl th)),
    REPEAT STRIP_TAC THEN REWRITE_TAC[th] THEN
    MP_TAC (SPEC_ALL C975E_COMPULSORY) THEN ASM_REWRITE_TAC[c975e_compulsory] THEN SIMP_TAC[]);;

let C975IC_AUXPTS = map oo_aux_point (0 -- 19);;

let c975ic_pull tms [c; s; u; v; a] =
  map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms;;
let c975ic_pullx = c975ic_pull [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;

(* Lean: foreign (private): goal ~linside (owner m) x y, from a point of owner n *)
let C975IC_FOREIGN_TAC n th (asl, w) =
  let args = snd (strip_comb (dest_neg w)) in
  let m = dest_small_numeral (el 5 (snd (strip_comb (hd args)))) in
  (MP_TAC (SPEC_ALL (oo_apart C975D_F m n)) THEN ASM_REWRITE_TAC[ldisj] THEN
   DISCH_THEN (MP_TAC o SPECL [el 5 args; el 6 args]) THEN
   ASM_SIMP_TAC[th] THEN NO_TAC) (asl, w);;

let C975IC_SIDE_TAC ths fors =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_SIMP_TAC (ths @ [OO_BOX]) THEN NO_TAC;
         REPEAT (FIRST [MATCH_MP_TAC LCONT_PULLSW; MATCH_MP_TAC LCONT_PULLX; MATCH_MP_TAC LCONT_PULLY]) THEN
         ASM_SIMP_TAC[OO_BOX] THEN NO_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
         FIRST [ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC;
                ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC];
         MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
         ASM_REWRITE_TAC C975IC_AUXPTS THEN NO_TAC;
         FIRST (map (fun (n, th) -> C975IC_FOREIGN_TAC n th) fors)];;

(* apply a geometry lemma to (pulled) owner tuples: the goal is its conclusion *)
let C975IC_APPLY_TAC th tp ths fors =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
                       REAL_RAT_REDUCE_CONV) (SPECL tp th) in
  MATCH_MP_TAC th' THEN REPEAT CONJ_TAC THEN C975IC_SIDE_TAC ths fors;;

(* the same for a lemma with conclusion F *)
let C975IC_CONTRA_TAC th tp ths fors =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC
                       REAL_RAT_REDUCE_CONV) (SPECL tp th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  SUBGOAL_THEN (lhand (concl th')) (fun h -> ACCEPT_TAC (MP th' h)) THEN
  REPEAT CONJ_TAC THEN C975IC_SIDE_TAC ths fors;;

let C975IC_COMPULSORY_TAC =
  MP_TAC (SPEC_ALL C975E_COMPULSORY) THEN ASM_REWRITE_TAC[c975e_compulsory] THEN
  DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

(* a propositional consequence of the listed assumptions *)
let C975IC_BY_TAC tm asms =
  SUBGOAL_THEN tm ASSUME_TAC THENL
   [MAP_EVERY (MP_TAC o ASSUME) asms THEN CONV_TAC TAUT; ALL_TAC];;

let C975IC_NE_MARKER = c975ic_seed 1024 (`&47 / &20`, `&47 / &20`);;
let C975IC_TOP_MARKER = c975ic_seed 34816 (`&2`, `&1543 / &500`);;
let C975IC_NW_MARKER = c975ic_seed 34816 (`&33 / &20`, `&47 / &20`);;
let C975IC_CORNER = c975ic_seed 48 (`&3`, `&3`);;
let C975IC_R_MARKER = c975ic_seed 16384 (`&1543 / &500`, `&2`);;
let C975IC_SE_MARKER = c975ic_seed 512 (`&47 / &20`, `&33 / &20`);;
let C975IC_R_HIGH = c975ic_aux 16384 19;;
let C975IC_SE_OUTWARD = c975ic_aux 512 8;;
let C975IC_TOP_G4 = c975ic_aux 34816 14;;

(* Lean: not_top_inward *)
let C975IC_NOT_TOP_INWARD = prove
 (c975ic_stmt [] (mk_neg (c975ic_mem 5 34816)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN C975IC_COMPULSORY_TAC THEN
  OO_EXCLUDE_ALL_TAC C975D_F 1024 THEN
  C975IC_BY_TAC (c975ic_mem 7 1024)
    [mk_disj(c975ic_mem 5 1024, c975ic_mem 7 1024); mk_neg (c975ic_mem 5 1024)] THEN
  C975IC_CONTRA_TAC FCTMI_SHORT_IMPOSSIBLE (c975ic_owner 34816 @ c975ic_owner 1024 @ c975ic_owner 16384)
   [C975IC_TOP_MARKER; C975IC_NE_MARKER; C975IC_R_MARKER; C975IC_R_HIGH;
    oo_apart C975D_F 34816 1024; oo_apart C975D_F 1024 16384]
   [48, C975IC_CORNER; 512, C975IC_SE_OUTWARD]);;

(* Lean: remaining_top *)
let C975IC_REMAINING_TOP = prove
 (c975ic_stmt [] (mk_disj(c975ic_mem 3 34816, c975ic_mem 7 34816)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C975E_TOP_ALTERNATIVES) THEN MP_TAC (SPEC_ALL C975IC_NOT_TOP_INWARD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC TAUT);;

(* Lean: top_seven_incoming *)
let C975IC_TOP_SEVEN_INCOMING = prove
 (c975ic_stmt [c975ic_mem 7 34816] (mk_conj(c975ic_mem 5 1024, c975ic_mem 16 1024)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C975IC_COMPULSORY_TAC THEN
  SUBGOAL_THEN (c975ic_own 34816 `&113 / &50` `&3`) MP_TAC THENL
   [MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [`&87 / &50`; `&12 / &5`] THEN
    ASM_REWRITE_TAC C975IC_AUXPTS THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC C975IC_AUXPTS THEN DISCH_TAC THEN
  OO_EXCLUDE_ALL_TAC C975D_F 1024 THEN
  MAP_EVERY (MP_TAC o ASSUME)
   [mk_disj(c975ic_mem 5 1024, c975ic_mem 7 1024); mk_disj(c975ic_mem 16 1024, c975ic_mem 17 1024);
    mk_neg (c975ic_mem 7 1024); mk_neg (c975ic_mem 17 1024)] THEN
  CONV_TAC TAUT);;

(* Lean: right_high *)
let C975IC_RIGHT_HIGH = prove
 (c975ic_stmt [] (c975ic_own 16384 `&3` `&64 / &25`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975IC_APPLY_TAC FCWHM_POINT (c975ic_pullx (c975ic_owner 16384))
   [C975IC_R_MARKER; C975IC_R_HIGH] [512, C975IC_SE_OUTWARD; 1024, C975IC_NE_MARKER]);;

(* the mid point of the right bar (Lean: rightMid in incoming_high) *)
let C975IC_RIGHT_MID = prove
 (c975ic_stmt [] (c975ic_own 16384 `&3` `&5 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&12 / &5`; `&64 / &25`] THEN
  ASM_SIMP_TAC[C975IC_R_HIGH; C975IC_RIGHT_HIGH] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: incoming_high *)
let C975IC_INCOMING_HIGH = prove
 (c975ic_stmt [mk_conj(c975ic_mem 5 1024, c975ic_mem 16 1024)] (c975ic_own 1024 `&2` `&5 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975IC_APPLY_TAC C981CP_POINT (c975ic_owner 1024)
   [C975IC_NE_MARKER]
   [512, C975IC_SE_MARKER; 34816, C975IC_NW_MARKER; 16384, C975IC_R_HIGH; 16384, C975IC_RIGHT_MID]);;

(* incoming_high after top_seven_incoming (used in top_left) *)
let C975IC_SEVEN_HIGH = prove
 (c975ic_stmt [c975ic_mem 7 34816] (c975ic_own 1024 `&2` `&5 / &2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C975IC_INCOMING_HIGH THEN
  ASM_SIMP_TAC[C975IC_TOP_SEVEN_INCOMING]);;

(* Lean: top_left *)
let C975IC_TOP_LEFT = prove
 (c975ic_stmt [] (c975ic_mem 3 34816),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C975IC_REMAINING_TOP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (DISJ_CASES_THEN ASSUME_TAC) THEN TRY (FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[GSYM (oo_aux_point 3)] THEN
  C975IC_APPLY_TAC FCTPP_POINT (c975ic_owner 34816)
   [C975IC_NW_MARKER] [1024, C975IC_NE_MARKER; 1024, C975IC_SEVEN_HIGH]);;

(* Lean: not_top_elbow (the triangle certificate as a convex combination) *)
let C975IC_NOT_TOP_ELBOW = prove
 (c975ic_stmt [] (mk_neg (c975ic_mem 16 34816)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC (SPEC_ALL C975IC_NOT_TOP_INWARD) THEN ASM_REWRITE_TAC[GSYM (oo_aux_point 5)] THEN
  MP_TAC (SPEC_ALL C975IC_NW_MARKER) THEN MP_TAC (SPEC_ALL C975IC_TOP_MARKER) THEN
  UNDISCH_TAC (c975ic_mem 16 34816) THEN REWRITE_TAC[GSYM (oo_aux_point 16)] THEN
  ASM_REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: top_g_checked (private) *)
let C975IC_TOP_G_CHECKED = prove
 (`forall s. MEM s c975d_topGAllowed ==> ~(1 IN s) ==> ~(3 IN s) ==> ~(6 IN s) ==> s = {4} \/ s = {4,7}`,
  OO_LIST_CUT_TAC [c975d_topGAllowed]);;

let c975ic_gown m =
  let iv = list_mk_comb(`oidx`, C975IC_V5 @ [mk_small_numeral m]) in
  list_mk_comb(`auxown`, [`1`] @ map (fun f -> mk_comb(f, iv))
    [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`] @ [`l:real`]);;

(* Lean: top_g_options *)
let C975IC_TOP_G_OPTIONS = prove
 (c975ic_stmt [] (mk_disj(mk_eq(c975ic_gown 34816, `{4}`), mk_eq(c975ic_gown 34816, `{4,7}`))),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C975IC_COMPULSORY_TAC THEN
  MP_TAC (SPEC_ALL C975IC_NOT_TOP_ELBOW) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OO_EXCLUDE_ALL_TAC C975D_F 34816 THEN
  MATCH_MP_TAC (REWRITE_RULE[IMP_IMP] C975IC_TOP_G_CHECKED) THEN
  REWRITE_TAC[C975E_G_COMBINED] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HDOM_OWNER THEN EXISTS_TAC C975D_F THEN
  ASM_REWRITE_TAC[C975D_TOPG; in_fam 34816 C975D_F]);;

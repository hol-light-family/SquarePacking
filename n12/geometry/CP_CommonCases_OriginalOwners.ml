(* ========================================================================= *)
(* Phase 2: Compact/Completion/CommonCases/OriginalOwners.lean.              *)
(*                                                                           *)
(* The owner of a mask of the actual family, as a 5-tuple square:          *)
(*   Lean  owner p mask        (ooc c1 c2 a b l m) (oos c1 c2 a b l m)      *)
(*                             (oou c1 c2 a b l m) (oov c1 c2 a b l m) l     *)
(*   Lean  auxiliaries p mask  ooaux c1 c2 a b l m                           *)
(*   Lean  hf : codedMarkerFamily p = family, hm : mask IN family            *)
(*         NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\   *)
(*         m IN fam                                                          *)
(* (definitions in PackingContext.ml).  Statements about literal data are   *)
(* OCaml producers:                                                          *)
(*   oo_seed m (x, y)        Lean seed            (PackingContext.ml)        *)
(*   oo_known m owned (x, y) Lean known_point     (PackingContext.ml)        *)
(*   oo_missing m k          Lean missing_marker at a literal marker         *)
(*   oo_aux_point j          Lean auxiliary_exact at a literal index         *)
(*   cdom_cache th al        Lean cached_domain                              *)
(*   oo_restrict23 th        Lean restrict_budget23 (evaluated)              *)
(* ========================================================================= *)

needs "n12/geometry/PackingContext.ml";;
needs "n12/geometry/RelaxedOwnerDomain.ml";;

(* Lean: code *)
let OO_CODE = prove
 (`forall c1 c2 a b l fam m. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam
     ==> oidx c1 c2 a b l m < 12 /\
         ownmask (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m))
                 (a (oidx c1 c2 a b l m)) (b (oidx c1 c2 a b l m)) l = m`,
  MESON_TAC[OIDX_LT; OIDX_SPEC]);;

(* Lean: side  ((owner p mask).side = l) *)
let OO_SIDE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> &1 < l`,
  MESON_TAC[NPACK_SQ; ARITH_RULE `0 < 12`]);;

(* the remaining OpenSquare fields of the owner (Lean: p.side_le, unit_normal) *)
let OO_SIDE_LE = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l ==> l <= &1001 / &1000`,
  MESON_TAC[NPACK_SQ; ARITH_RULE `0 < 12`]);;

let OO_UNIT = prove
 (`forall c1 c2 a b l m. NPACK c1 c2 a b l
     ==> ooc c1 c2 a b l m * ooc c1 c2 a b l m + oos c1 c2 a b l m * oos c1 c2 a b l m = &1`,
  REWRITE_TAC[ooc; oos] THEN MESON_TAC[NPACK_SQ; OIDX_LT]);;

let OO_LSQUARE = prove
 (`forall c1 c2 a b l m. NPACK c1 c2 a b l
     ==> lsquare (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lsquare] THEN ASM_SIMP_TAC[OO_UNIT] THEN
  MP_TAC(SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: box *)
let OO_BOX = prove
 (`forall c1 c2 a b l m. NPACK c1 c2 a b l
     ==> lcont (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ooc; oos; oou; oov] THEN MATCH_MP_TAC OWALLS_LCONT THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `oidx c1 c2 a b l m`] NPACK_SQ) THEN
  ASM_REWRITE_TAC[OIDX_LT] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: coded_exact at the owner (ExactMarkers (owner p mask) (maskSupport mask)) *)
let OO_MARKERS = prove
 (`forall c1 c2 a b l fam m. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam
     ==> forall k. k < 16
         ==> (linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                      (marker k$1) (marker k$2) <=> k IN bitset m)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM OO_OSQ] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `m:num`] OIDX_OWNED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[owned; IN_ELIM_THM]);;

(* Lean: missing_marker *)
let OO_MISSING = prove
 (`forall c1 c2 a b l fam m k. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\ m IN fam /\
       k < 16 /\ ~(k IN bitset m)
     ==> ~linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                  (marker k$1) (marker k$2)`,
  MESON_TAC[OO_MARKERS]);;

(* missing_marker at a literal marker k not in m:
   |- !c1 c2 a b l fam. NPACK .. /\ IMAGE .. = fam /\ m IN fam ==> ~linside (owner m) x_k y_k *)
let oo_missing m k =
  if mem k (bits m) || k > 15 then failwith "oo_missing: marker owned" else
  let th = SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `fam:num->bool`; mk_small_numeral m; mk_small_numeral k] OO_MISSING in
  let lt = EQT_ELIM (NUM_REDUCE_CONV (mk_binop `(<):num->num->bool` (mk_small_numeral k) `16`)) in
  let nin = EQT_ELIM ((REWRITE_CONV[bitset_bits m; IN_SET_OF_LIST; MEM] THENC NUM_REDUCE_CONV THENC
                       REWRITE_CONV[])
                      (mk_neg(mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral k), bitset_tm m)))) in
  let hyp = oo_hyp m in
  let h = ASSUME hyp in
  let th = MP th (CONJ (CONJUNCT1 h) (CONJ (CONJUNCT1 (CONJUNCT2 h)) (CONJ (CONJUNCT2 (CONJUNCT2 h)) (CONJ lt nin)))) in
  let th = CONV_RULE (RAND_CONV (REWRITE_CONV[MARKER_EXPLICIT; VECTOR_2])) th in
  GENL OO_VARS (DISCH hyp th);;

(* Lean: apart *)
let OO_APART = prove
 (`forall c1 c2 a b l fam m n. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
       m IN fam /\ n IN fam /\ ~(m = n)
       ==> ldisj (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                 (ooc c1 c2 a b l n) (oos c1 c2 a b l n) (oou c1 c2 a b l n) (oov c1 c2 a b l n) l`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ooc; oos; oou; oov] THEN MATCH_MP_TAC NPACK_LDISJ THEN
  ASM_REWRITE_TAC[OIDX_LT] THEN ASM_MESON_TAC[OIDX_INJ]);;

(* Lean: auxiliary_disjoint *)
let OO_AUXILIARY_DISJOINT = OO_AUX_DISJOINT;;

(* Lean: auxiliary_exact *)
let OO_AUXILIARY_EXACT = OO_AUX_EXACT;;

(* Lean: domain *)
let OO_DOMAIN = CDOM_OWNER;;

(* Lean: cached_domain (any list containing the domain's entries, as sets) *)
let OO_CACHED_DOMAIN = CDOM_MONO;;

(* Lean: restrict_budget23 *)
let OO_RESTRICT_BUDGET23 = prove
 (`forall fam m al. cdom fam m al /\ CARD (fam INTER auxex 0) = 3 /\ CARD (fam INTER auxex 1) = 2 /\
     ~(m IN auxex 0) /\ ~(m IN auxex 1)
     ==> cdom fam m (FILTER (\s. CARD (rofirst s) <= 2 /\ CARD (rosecond s) = 1) al)`,
  REWRITE_TAC[cdom; MEM_FILTER] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`] THEN
  STRIP_TAC THEN BETA_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[RO_HALVES] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `fam:num->bool`; `0`; `i:num`] PK_BUDGET) THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `fam:num->bool`; `1`; `i:num`] PK_BUDGET) THEN
    ASM_REWRITE_TAC[ARITH_RULE `0 < 2 /\ 1 < 2`; pkup; pklow] THEN ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* restrict_budget23, evaluated on a literal domain theorem *)
let oo_restrict23 th =
  let (fam, m, _) = cdom_parts th in
  let card k n = EQT_ELIM ((REWRITE_CONV[card_exempt fam k]) (mk_eq(mk_comb(`CARD:(num->bool)->num`,
             mk_binop `(INTER):(num->bool)->(num->bool)->(num->bool)` fam
               (mk_comb(`auxex`, mk_small_numeral k))), mk_small_numeral n))) in
  let ne k = EQF_ELIM (AUXEX_CONV (mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral m),
                                           mk_comb(`auxex`, mk_small_numeral k)))) in
  CONV_RULE (RAND_CONV (ro_filter_conv fam m))
    (MATCH_MP OO_RESTRICT_BUDGET23 (end_itlist CONJ [th; card 0 3; card 1 2; ne 0; ne 1]));;

(* Lean: horizontal_segment *)
let OO_BETWEEN = prove
 (`forall c x0 x1 x. x0 <= x /\ x <= x1
     ==> (c * x0 <= c * x /\ c * x <= c * x1) \/ (c * x1 <= c * x /\ c * x <= c * x0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `&0 <= c` THENL
   [DISJ1_TAC THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
    DISJ2_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH `a * b <= a * c <=> --a * c <= --a * b`] THEN
    CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC]);;

let OO_HORIZONTAL_SEGMENT = prove
 (`forall c s u v a x0 x1 y x. linside c s u v a x0 y /\ linside c s u v a x1 y /\ x0 < x1 /\
       x0 <= x /\ x <= x1 ==> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `x0:real`; `x1:real`; `x:real`] OO_BETWEEN) THEN
  MP_TAC(SPECL [`--s:real`; `x0:real`; `x1:real`; `x:real`] OO_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: vertical_segment *)
let OO_VERTICAL_SEGMENT = prove
 (`forall c s u v a x y0 y1 y. linside c s u v a x y0 /\ linside c s u v a x y1 /\ y0 < y1 /\
       y0 <= y /\ y <= y1 ==> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `y0:real`; `y1:real`; `y:real`] OO_BETWEEN) THEN
  MP_TAC(SPECL [`c:real`; `y0:real`; `y1:real`; `y:real`] OO_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Support for the "OriginalData" pattern  masks : Fin 12 -> Nat,           *)
(* owners p i := owner p (masks i): take a HOL list L of the masks and use   *)
(* EL i L (i < 12).  oo_list_facts fam L proves the two decide facts        *)
(* (Lean: member, injective).                                                *)
(* ------------------------------------------------------------------------- *)

let PAIRWISE_DISTINCT_EL = prove
 (`forall L:num list i j. PAIRWISE (\x y. ~(x = y)) L /\ i < LENGTH L /\ j < LENGTH L /\ EL i L = EL j L
     ==> i = j`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT; PAIRWISE] THEN REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC (SPEC `i:num` num_CASES) THEN STRUCT_CASES_TAC (SPEC `j:num` num_CASES) THEN
  REWRITE_TAC[EL; HD; TL; LT_SUC; SUC_INJ; NOT_SUC; LT_0; GSYM ALL_MEM] THEN
  ASM_MESON_TAC[MEM_EL]);;

let OO_LIST_MEMBER = prove
 (`forall fam L i. ALL (\m. m IN fam) L /\ i < LENGTH L ==> EL i L IN fam`,
  REWRITE_TAC[GSYM ALL_MEM] THEN MESON_TAC[MEM_EL]);;

(* Lean (OriginalData files): apart for indices of the mask list *)
let OO_LIST_APART = prove
 (`forall c1 c2 a b l fam L i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     ALL (\m. m IN fam) L /\ PAIRWISE (\x y. ~(x = y)) L /\
     i < LENGTH L /\ j < LENGTH L /\ ~(i = j)
     ==> ldisj (ooc c1 c2 a b l (EL i L)) (oos c1 c2 a b l (EL i L)) (oou c1 c2 a b l (EL i L))
               (oov c1 c2 a b l (EL i L)) l
               (ooc c1 c2 a b l (EL j L)) (oos c1 c2 a b l (EL j L)) (oou c1 c2 a b l (EL j L))
               (oov c1 c2 a b l (EL j L)) l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_APART THEN EXISTS_TAC `fam:num->bool` THEN
  ASM_MESON_TAC[OO_LIST_MEMBER; PAIRWISE_DISTINCT_EL]);;

let OO_LIST_AUX_DISJOINT = prove
 (`forall c1 c2 a b l fam L i j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     ALL (\m. m IN fam) L /\ PAIRWISE (\x y. ~(x = y)) L /\
     i < LENGTH L /\ j < LENGTH L /\ ~(i = j)
     ==> DISJOINT (ooaux c1 c2 a b l (EL i L)) (ooaux c1 c2 a b l (EL j L))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_AUX_DISJOINT THEN EXISTS_TAC `fam:num->bool` THEN
  ASM_MESON_TAC[OO_LIST_MEMBER; PAIRWISE_DISTINCT_EL]);;

(* |- ALL (\m. m IN fam) L  and  |- PAIRWISE (\x y. ~(x = y)) L  for literal fam, L *)
let oo_list_facts fam L =
  let all = EQT_ELIM ((REWRITE_CONV[ALL] THENC DEPTH_CONV BETA_CONV THENC
                       REWRITE_CONV (fam_defs fam @ [IN_INSERT; NOT_IN_EMPTY; IN_SET_OF_LIST; MEM]) THENC
                       NUM_REDUCE_CONV THENC REWRITE_CONV[])
                      (list_mk_comb(`ALL:(num->bool)->(num)list->bool`,
                         [mk_abs(`m:num`, mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `m:num`), fam)); L]))) in
  let pw = EQT_ELIM ((REWRITE_CONV[PAIRWISE; ALL] THENC DEPTH_CONV BETA_CONV THENC NUM_REDUCE_CONV THENC
                      REWRITE_CONV[])
                     (list_mk_comb(`PAIRWISE:(num->num->bool)->(num)list->bool`, [`\x y:num. ~(x = y)`; L]))) in
  (all, pw);;

(* instantiate an owner producer theorem at a literal (or named) family F:
     |- !c1 c2 a b l fam. NPACK .. /\ IMAGE .. = fam /\ m IN fam [/\ rest] ==> P
   becomes
     |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP c1 c2 a b l) = F [/\ rest] ==> P *)
let oo_inst fam th =
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let th1 = SPEC fam (SPECL vars th) in
  let ant = lhand (concl th1) in
  let np = lhand ant and r1 = rand ant in
  let row = lhand r1 and r2 = rand r1 in
  let (inm, rest) = if is_conj r2 then (lhand r2, Some (rand r2)) else (r2, None) in
  let inth = in_fam (dest_small_numeral (lhand inm)) fam in
  let newant = match rest with None -> mk_conj(np, row) | Some r -> mk_conj(np, mk_conj(row, r)) in
  let h = ASSUME newant in
  let old = match rest with
      None -> CONJ (CONJUNCT1 h) (CONJ (CONJUNCT2 h) inth)
    | Some _ -> CONJ (CONJUNCT1 h) (CONJ (CONJUNCT1 (CONJUNCT2 h)) (CONJ inth (CONJUNCT2 (CONJUNCT2 h)))) in
  GENL vars (DISCH newant (MP th1 old));;

(* ------------------------------------------------------------------------- *)
(* Toolkit for owner-domain arguments (Lean: domain + decide cuts).         *)
(* ------------------------------------------------------------------------- *)

(* apart at literal masks of a literal family:
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = F ==> ldisj (owner m) (owner n) *)
let oo_apart fam m n =
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let th = SPECL (vars @ [fam; mk_small_numeral m; mk_small_numeral n]) OO_APART in
  let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n))) in
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let h = ASSUME hyp in
  GENL vars (DISCH hyp (MP th (end_itlist CONJ [CONJUNCT1 h; CONJUNCT2 h; in_fam m fam; in_fam n fam; ne])));;

let OO_IN_CONV = REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY] THENC NUM_REDUCE_CONV THENC REWRITE_CONV[];;

(* With assumptions  NPACK c1 c2 a b l  and  IMAGE binarysum (FFP c1 c2 a b l) = F,
   split the goal over the allowed sets of |- cdom F m al: in each case
   ooaux c1 c2 a b l m = S is assumed and rewritten (with literal membership
   evaluated) in the goal and the assumptions; cases with a false assumption close. *)
let OO_DOMAIN_CASES_TAC dth (asl, w) =
  let (fam, m, _) = cdom_parts dth in
  let find_asm p = snd (find (fun (_, th) -> p (concl th)) asl) in
  let hnp = find_asm (fun c -> is_comb c && fst (strip_comb c) = `NPACK`) in
  let hrow = find_asm (fun c -> is_eq c && rhs c = fam) in
  let mem = MATCH_MP CDOM_OWNER (end_itlist CONJ [dth; hnp; hrow; in_fam m fam]) in
  let dj = CONV_RULE (REWRITE_CONV (fam_defs (rand (concl dth)) @ [MEM])) mem in
  let case th =
    RULE_ASSUM_TAC (CONV_RULE (TRY_CONV (REWRITE_CONV[th] THENC OO_IN_CONV))) THEN ASSUME_TAC th THEN
    CONV_TAC (REWRITE_CONV[th] THENC OO_IN_CONV) THEN
    TRY (FIRST_ASSUM (fun f -> if concl f = `false` then CONTR_TAC f else NO_TAC)) in
  (MP_TAC dj THEN DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN (fun th ->
     if concl th = `false` then CONTR_TAC th else case th))) (asl, w);;

(* ~(j IN ooaux c1 c2 a b l m) from an assumption  linside (owner n) x_j y_j  (point j owned by n) *)
let OO_ABSENT_TAC fam m j n =
  let xy = let args = snd (strip_comb (lhand (concl (SPEC_ALL (oo_aux_point j))))) in [el 5 args; el 6 args] in
  SUBGOAL_THEN (mk_neg (mk_comb (mk_comb (`(IN):num->(num->bool)->bool`, mk_small_numeral j), ooaux_tm m)))
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM (oo_aux_point j)] THEN DISCH_TAC THEN
    MP_TAC (SPEC_ALL (oo_apart fam m n)) THEN ASM_REWRITE_TAC[ldisj] THEN
    DISCH_THEN (MP_TAC o SPECL xy) THEN ASM_REWRITE_TAC[];
    ALL_TAC];;

(* a point owned by owner n is not inside owner m (apart):
   thn: |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = F ==> linside (owner n) x y
   |- !c1 c2 a b l. NPACK .. /\ IMAGE binarysum (FFP ..) = F ==> ~linside (owner m) x y *)
let oo_excl fam m n thn =
  let vars = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let th = SPECL vars thn in
  let hyp = lhand (concl th) in
  let h = ASSUME hyp in
  let bth = MP th h in
  let args = snd (strip_comb (concl bth)) in
  let d = MP (SPECL vars (oo_apart fam m n)) h in
  let d2 = SPECL [el 5 args; el 6 args] (REWRITE_RULE[ldisj] d) in
  let a = lhand (rand (concl d2)) in
  GENL vars (DISCH hyp (NOT_INTRO (DISCH a (MP (NOT_ELIM d2) (CONJ (ASSUME a) bth)))));;

(* ------------------------------------------------------------------------- *)
(* More toolkit (batch 2).                                                   *)
(* ------------------------------------------------------------------------- *)

(* Lean (C702 / C48): pair_from_points *)
let OO_PAIR_FROM_POINTS = prove
 (`forall c1 c2 a b l m i j. i < 20 /\ j < 20 /\
     linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
             (EL i (AUXPTS 2)$1) (EL i (AUXPTS 2)$2) /\
     linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
             (EL j (AUXPTS 2)$1) (EL j (AUXPTS 2)$2)
     ==> {i, j} SUBSET ooaux c1 c2 a b l m`,
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN MESON_TAC[OO_AUX_EXACT]);;

(* Lean (C702): some_auxiliary, for any family *)
let OO_SOME_AUXILIARY = prove
 (`forall c1 c2 a b l fam m k. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     m IN fam /\ k < 2 /\ ~(m IN auxex k)
     ==> exists j. j < 10 /\
             linside (ooc c1 c2 a b l m) (oos c1 c2 a b l m) (oou c1 c2 a b l m) (oov c1 c2 a b l m) l
                     (EL j (AUXPTS k)$1) (EL j (AUXPTS k)$2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `k:num`; `oidx c1 c2 a b l m`] PK_BUDGET) THEN
  ASM_REWRITE_TAC[OIDX_LT] THEN
  SUBGOAL_THEN `ownmask (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m)) (a (oidx c1 c2 a b l m))
                        (b (oidx c1 c2 a b l m)) l = m` SUBST1_TAC THENL
   [MATCH_MP_TAC OIDX_SPEC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[pklow] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
  SIMP_TAC[CARD_EQ_0; FINITE_AUXOWN; GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `j:num`) THEN EXISTS_TAC `j:num` THEN
  MP_TAC(MATCH_MP AUXOWN_SUBSET10 (ASSUME `k < 2`)) THEN
  DISCH_THEN(MP_TAC o SPEC `j:num` o REWRITE_RULE[SUBSET; IN_ELIM_THM] o
    SPECL [`c1 (oidx c1 c2 a b l m):real`; `c2 (oidx c1 c2 a b l m):real`; `a (oidx c1 c2 a b l m):real`;
           `b (oidx c1 c2 a b l m):real`; `l:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `j IN auxown k (c1 (oidx c1 c2 a b l m)) (c2 (oidx c1 c2 a b l m)) (a (oidx c1 c2 a b l m))
                        (b (oidx c1 c2 a b l m)) l` THEN
  REWRITE_TAC[auxown; IN_ELIM_THM; OO_OSQ] THEN SIMP_TAC[]);;

(* add  ~(j IN ooaux .. m)  for every assumption  j IN ooaux .. n  with n <> m
   (needs assumptions NPACK c1 c2 a b l and IMAGE binarysum (FFP ..) = fam) *)
let OO_EXCLUDE_ALL_TAC fam m (asl, w) =
  let find_asm p = snd (find (fun (_, th) -> p (concl th)) asl) in
  let hnp = find_asm (fun c -> is_comb c && fst (strip_comb c) = `NPACK`) in
  let hrow = find_asm (fun c -> is_eq c && rhs c = fam) in
  let mem_of c =
    if is_binop `(IN):num->(num->bool)->bool` c then
      let s = rand c in
      let (f, args) = strip_comb s in
      if f = `ooaux` && length args = 6 && is_numeral (el 5 args) then Some (lhand c, dest_small_numeral (el 5 args))
      else None
    else None in
  let news = List.concat (map (fun (_, th) ->
      match mem_of (concl th) with
        Some (j, n) when n <> m ->
          let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n))) in
          let d = MATCH_MP OO_AUX_DISJOINT (end_itlist CONJ [hnp; hrow; in_fam m fam; in_fam n fam; ne]) in
          let d' = SPEC j (REWRITE_RULE[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] d) in
          [NOT_INTRO (DISCH (mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, j), ooaux_tm m))
             (MP (NOT_ELIM d') (CONJ (ASSUME (mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, j), ooaux_tm m))) th)))]
      | _ -> []) asl) in
  MAP_EVERY ASSUME_TAC news (asl, w);;

(* a domain theorem with a named allowed list:  def: |- name = [..] *)
let cdom_named th def = CONV_RULE (RAND_CONV (REWR_CONV (SYM def))) (cdom_cache th (rhs (concl def)));;
let hdom_named th def = CONV_RULE (RAND_CONV (REWR_CONV (SYM def))) (hdom_cache th (rhs (concl def)));;

(* cut lemmas over a named list:  !s. MEM s name /\ hyps ==> concl  (memberships decided) *)
let OO_LIST_CUT_TAC defs =
  REWRITE_TAC (defs @ [MEM; IMP_CONJ]) THEN GEN_TAC THEN
  DISCH_THEN (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC OO_IN_CONV;;

(* prove memberships  j IN ooaux .. m  in order, each from the domain of m (assoc list
   doms : (mask, |- cdom fam mask al) list) after excluding the indices owned elsewhere;
   each step is added as an assumption; then the goal is closed by rewriting *)
let OO_CHAIN_TAC fam doms steps =
  MAP_EVERY (fun (m, js) ->
    let t = list_mk_conj (map (fun j -> mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j),
                                                ooaux_tm m)) js) in
    SUBGOAL_THEN t STRIP_ASSUME_TAC THENL
     [OO_EXCLUDE_ALL_TAC fam m THEN OO_DOMAIN_CASES_TAC (assoc m doms); ALL_TAC]) steps THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN ASM_REWRITE_TAC[];;

(* goal  j IN ooaux c1 c2 a b l m  from seeds of m: the aux point j is the seed
   pts = [p], or lies on the horizontal / vertical segment between pts = [p0; p1];
   needs assumptions NPACK .. and IMAGE binarysum (FFP ..) = fam *)
let OO_SEED_MEM_TAC fam m j pts =
  let seeds = map (fun p -> oo_inst fam (oo_seed m p)) pts in
  let fin = ASM_SIMP_TAC seeds THEN CONV_TAC REAL_RAT_REDUCE_CONV in
  REWRITE_TAC[GSYM (oo_aux_point j)] THEN
  (match pts with
     [_] -> ASM_SIMP_TAC seeds
   | [(x0, y0); (x1, y1)] ->
       if y0 = y1 then MATCH_MP_TAC OO_HORIZONTAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [x0; x1] THEN fin
       else MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN MAP_EVERY EXISTS_TAC [y0; y1] THEN fin
   | _ -> failwith "OO_SEED_MEM_TAC");;

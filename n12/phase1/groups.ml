(* ========================================================================= *)
(* Port, layer 2: the set of markers owned by one square is one of the 103   *)
(* candidate groups (Jatloe: Diameter.lean, MarkerClassification.lean).      *)
(* Groups are coded as bit masks with HOL's binarysum.                        *)
(* ========================================================================= *)

needs "n12/phase1/normalize.ml";;
needs "Library/binary.ml";;
loadt "n12/phase1/groups_data.ml";;

let owned = new_definition
 `owned c1 c2 a b l = {k | k < 16 /\ marker k IN osq c1 c2 a b l}`;;

let ownmask = new_definition
 `ownmask c1 c2 a b l = binarysum (owned c1 c2 a b l)`;;

let OSQ_DIAMETER = prove
 (`forall c1 c2 a b l z w:real^2.
        a * a + b * b = &1 /\ z IN osq c1 c2 a b l /\ w IN osq c1 c2 a b l
        ==> (z$1 - w$1) * (z$1 - w$1) + (z$2 - w$2) * (z$2 - w$2) < &2 * l * l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[osq; IN_ELIM_THM] THEN STRIP_TAC THEN
  ABBREV_TAC `p = ((z:real^2)$1 - (w:real^2)$1) * a + ((z:real^2)$2 - (w:real^2)$2) * b` THEN
  ABBREV_TAC `q = ((z:real^2)$2 - (w:real^2)$2) * a - ((z:real^2)$1 - (w:real^2)$1) * b` THEN
  SUBGOAL_THEN `abs p < l /\ abs q < l` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `((z:real^2)$1 - (w:real^2)$1) * (z$1 - w$1) + (z$2 - w$2) * (z$2 - w$2) = p * p + q * q`
  SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["p"; "q"] THEN
    UNDISCH_TAC `a * a + b * b = &1` THEN CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`p:real`; `l:real`] REAL_LT_SQUARE_ABS) THEN
  MP_TAC(SPECL [`q:real`; `l:real`] REAL_LT_SQUARE_ABS) THEN
  SUBGOAL_THEN `abs l = l` (fun th -> REWRITE_TAC[th]) THENL
   [MATCH_MP_TAC(REAL_ARITH `abs p < l ==> abs l = l`) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

let MARKER_INCOMPAT = prove
 (`forall c1 c2 a b l i j.
        a * a + b * b = &1 /\ l <= &1001 / &1000 /\ &0 < l /\
        &2 * (&1001 / &1000) * (&1001 / &1000) <=
        (marker i$1 - marker j$1) * (marker i$1 - marker j$1) +
        (marker i$2 - marker j$2) * (marker i$2 - marker j$2)
        ==> ~(marker i IN osq c1 c2 a b l /\ marker j IN osq c1 c2 a b l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:real`; `c2:real`; `a:real`; `b:real`; `l:real`;
                `marker i`; `marker j`] OSQ_DIAMETER) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`l:real`; `&1001 / &1000`; `l:real`; `&1001 / &1000`] REAL_LE_MUL2) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Sums of distinct powers of two for an explicit increasing list.           *)

let BINARYSUM_LIST = prove
 (`forall L. sorted_lt L ==> binarysum (set_of_list L) = ITLIST (\k a. 2 EXP k + a) L 0`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[set_of_list; ITLIST; binarysum; NSUM_CLAUSES] THEN
  DISCH_TAC THEN SIMP_TAC[NSUM_CLAUSES; FINITE_SET_OF_LIST] THEN
  SUBGOAL_THEN `~((h:num) IN set_of_list t)` (fun th -> REWRITE_TAC[th]) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP INCR_ALL_LT) THEN
    REWRITE_TAC[GSYM ALL_MEM; IN_SET_OF_LIST] THEN MESON_TAC[LT_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM binarysum] THEN AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  UNDISCH_TAC `sorted_lt (CONS h t)` THEN SIMP_TAC[sorted_lt]);;

let SET_BITS_LIST = prove
 (`forall P L. ALL (\k. k < 16) L /\ (forall k. k < 16 ==> (P k <=> MEM k L))
         ==> {k | k < 16 /\ P k} = set_of_list L`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SET_OF_LIST] THEN
  ASM_MESON_TAC[ALL_MEM]);;

let pvar = `P:num->bool`;;
let pk k = mk_comb(pvar, mk_small_numeral k);;

let CLIQUE_TABLE =
  let pairfact (i,j) = mk_neg(mk_conj(pk i, pk j)) in
  let hyp = list_mk_conj(map pairfact INCOMPAT_PAIRS @
                         [`exists k. k < 16 /\ (P:num->bool) k`]) in
  let goal = mk_forall(pvar, mk_imp(hyp,
     `MEM (binarysum {k | k < 16 /\ (P:num->bool) k}) CANDMASKS`)) in
  let incompat k j = mem (k,j) INCOMPAT_PAIRS || mem (j,k) INCOMPAT_PAIRS in
  let leaf trues =
    if trues = [] then
      UNDISCH_TAC `exists k. k < 16 /\ (P:num->bool) k` THEN
      REWRITE_TAC[LT16_CASES; RIGHT_OR_DISTRIB; LEFT_OR_DISTRIB; EXISTS_OR_THM;
                  UNWIND_THM1; UNWIND_THM2] THEN
      ASM_REWRITE_TAC[]
    else
      let l = mk_list(map mk_small_numeral (List.rev trues), `:num`) in
      MP_TAC(ISPECL [pvar; l] SET_BITS_LIST) THEN ANTS_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[ALL] THEN CONV_TAC NUM_REDUCE_CONV;
          REWRITE_TAC[LT16_CASES] THEN GEN_TAC THEN
          DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
          ASM_REWRITE_TAC[MEM] THEN CONV_TAC NUM_REDUCE_CONV];
        DISCH_THEN SUBST1_TAC] THEN
      W(fun (_,w) -> MP_TAC(ISPEC l BINARYSUM_LIST)) THEN
      ANTS_TAC THENL
       [CONV_TAC(REWRITE_CONV[sorted_lt; HD; NOT_CONS_NIL] THENC NUM_REDUCE_CONV);
        DISCH_THEN SUBST1_TAC] THEN
      REWRITE_TAC[ITLIST; CANDMASKS; MEM] THEN CONV_TAC NUM_REDUCE_CONV in
  let rec dpll k trues forced =
    if k = 16 then leaf trues
    else if mem k forced then dpll (k+1) trues forced
    else
      let newf = filter (fun j -> j > k && incompat k j && not(mem j forced)) (0--15) in
      let force_tac =
        MAP_EVERY (fun j ->
          let pf = if mem (k,j) INCOMPAT_PAIRS then pairfact (k,j) else pairfact (j,k) in
          SUBGOAL_THEN (mk_neg(pk j)) ASSUME_TAC THENL
           [UNDISCH_TAC pf THEN ASM_REWRITE_TAC[]; ALL_TAC]) newf in
      ASM_CASES_TAC (pk k) THENL
       [force_tac THEN dpll (k+1) (k::trues) (newf @ forced);
        dpll (k+1) trues forced] in
  prove(goal, GEN_TAC THEN DISCH_THEN(MAP_EVERY ASSUME_TAC o CONJUNCTS) THEN dpll 0 [] []);;

let OWNMASK_IN_TABLE = prove
 (`forall c1 c2 a b l.
        &1 < l /\ l <= &1001 / &1000 /\ a * a + b * b = &1 /\ owalls c1 c2 a b l
        ==> MEM (ownmask c1 c2 a b l) CANDMASKS`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ownmask; owned] THEN
  MP_TAC(BETA_RULE(ISPEC `\k. marker k IN osq c1 c2 a b l` CLIQUE_TABLE)) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THEN
  FIRST [MATCH_MP_TAC MARKER_NONAVOID THEN ASM_REWRITE_TAC[] THEN NO_TAC;
         MATCH_MP_TAC MARKER_INCOMPAT THEN
         ASM_REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2] THEN
         CONJ_TAC THENL [ASM_REAL_ARITH_TAC; CONV_TAC REAL_RAT_REDUCE_CONV]]);;

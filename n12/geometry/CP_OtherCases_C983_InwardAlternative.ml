(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/InwardAlternative.lean.       *)
(* Complete exclusion of the original merged owner (owners p 7 = owner 2304) *)
(* with neither inward point F4, F5.  Conventions of                         *)
(* CP_OtherCases_C983_F5Filters.ml / InwardAlternativeEntrance.ml (owners    *)
(* p 1 -> 2, 4 -> 192, 7 -> 2304, 8 -> 4096, 11 -> 32768).  The Lean squares *)
(* (pullX q).translated x y are the tuples c983ia_trx (through               *)
(* OCOBP_INSIDE_TRANSLATED and LINSIDE_PULLX); owners_contained = OO_BOX     *)
(* (lcont); inside_segment = CES_INSIDE_SEGMENT.  ShortCornerAdvance.point = *)
(* OCSCA_POINT, TwoChordHull.points = OCTCH_POINTS, ShorterCornerWall.       *)
(* impossible = OCSCW_IMPOSSIBLE, no_merged_f5_top = C983IAE_NO_MERGED_F5_TOP,*)
(* left_aux / left_advance = C983AB_LEFT_AUX / C983AB_LEFT_ADVANCE.          *)
(* Tag C983IA_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_InwardAlternativeEntrance.ml";;
needs "n12/geometry/CP_OtherCases_TwoChordHull.ml";;
needs "n12/geometry/CP_OtherCases_ShortCornerAdvance.ml";;
needs "n12/geometry/CP_OtherCases_ShorterCornerWall.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;

(* the tuple of (pullX (owner m)).translated x y *)
let c983ia_trx m x y =
  let t = SPECL (c983fo_pull LINSIDE_PULLX m @ [x; y; `p:real`; `q:real`]) OCOBP_INSIDE_TRANSLATED in
  let args = snd (strip_comb (lhs (concl t))) in
  [el 0 args; el 1 args; el 2 args; el 3 args; el 4 args];;

let C983IA_CONV = REWRITE_CONV[OCOBP_INSIDE_TRANSLATED; LINSIDE_PULLX; REAL_NEG_MUL2] THENC
                  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* the antecedent conjunct of spec matching a predicate *)
let c983ia_ant spec p = find p (conjuncts (lhand (concl spec)));;
let c983ia_is_forall tm = is_forall tm;;

(* prove an antecedent tm under the packing hypotheses *)
let c983ia_side tm tac = UNDISCH_ALL (prove(mk_imp(C983F4F_NP, mk_imp(C983F4F_IMG, tm)),
  DISCH_TAC THEN DISCH_TAC THEN tac));;

(* the wall of a translated pullX owner from its containment *)
let c983ia_wall m =
  let np = ASSUME C983F4F_NP in
  let box = REWRITE_RULE[lcont] (MP (SPECL (C983E_VARS @ [mk_small_numeral m]) OO_BOX) np) in
  fun tm -> c983ia_side tm
    (REWRITE_TAC[OCOBP_INSIDE_TRANSLATED; LINSIDE_PULLX] THEN REPEAT GEN_TAC THEN
     DISCH_THEN(MP_TAC o MATCH_MP box) THEN REAL_ARITH_TAC);;

(* Lean: no_merged_f5_corner *)
let C983IA_NO_MERGED_F5_CORNER =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let noF5 = ASSUME (mk_neg (c983f4f_mem 5 7)) in
  let origin = seed 4 `&1` `&3` in
  let top = c983f4f_point (CONJUNCT1 (c983f5_use C983IAE_NO_MERGED_F5_TOP [noF5])) in
  let missingTop = excl 192 32768 top in
  let missingLeft = excl 192 4096 (MP (SPECL C983E_VARS C983AB_LEFT_ADVANCE) (c983f4f_hh ())) in
  let spec = SPECL (c983ia_trx 192 `&3` `&3`) OCSCA_POINT in
  let wall = c983ia_wall 192 (c983ia_ant spec c983ia_is_forall) in
  let th = c983sa_apply C983IA_CONV spec [unit 192; pos; side; wall; origin; missingTop; missingLeft] in
  c983f4f_close (c983sa_stmt [mk_neg (c983f4f_mem 5 7)] (c983ab_in 192 `&39 / &50` `&3`)) th;;

(* Lean: merged_west_hull *)
let C983IA_MERGED_WEST_HULL =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hh = c983f4f_hh () in
  let south = seed 7 `&33 / &20` `&33 / &20` and north = seed 7 `&33 / &20` `&47 / &20` in
  let marker = seed 8 `&457 / &500` `&2` in
  let missing4 = c983sa_missing 4 7 and missing5 = c983sa_missing 5 7 in
  let missingLow = excl 2304 2 (seed 1 `&1` `&87 / &50`) in
  let leftAux = MP (SPECL C983E_VARS C983AB_LEFT_AUX) hh in
  let missingHigh = excl 2304 4096 (CONJUNCT1 leftAux) in
  let spec = SPECL (c983ia_trx 2304 `&2` `&2`) OCTCH_POINTS in
  let segtm = c983ia_ant spec c983ia_is_forall in
  let seg = c983ia_side segtm
    (REWRITE_TAC[OCOBP_INSIDE_TRANSLATED; LINSIDE_PULLX] THEN
     X_GEN_TAC `z:real` THEN DISCH_TAC THEN DISCH_TAC THEN
     SUBGOAL_THEN `&4 - (&2 + ((&1 - z) * (&543 / &500) + z)) = (&1 - z) * (&457 / &500) + z * &1 /\
                   &2 + z * (&13 / &50) = (&1 - z) * &2 + z * (&113 / &50)` (fun th -> REWRITE_TAC[th])
     THENL [REAL_ARITH_TAC; ALL_TAC] THEN
     MP_TAC (SPECL (c983ab_own 4096 @ [`&457 / &500`; `&2`; `&1`; `&113 / &50`; `z:real`])
               CES_INSIDE_SEGMENT) THEN
     ASM_REWRITE_TAC[marker; CONJUNCT1 leftAux] THEN
     (let pt = list_mk_comb(`linside`, c983ab_own 4096 @
                 [`(&1 - z) * (&457 / &500) + z * &1`; `(&1 - z) * &2 + z * (&113 / &50)`]) in
      MATCH_ACCEPT_TAC (DISCH pt (excl 2304 4096 (ASSUME pt))))) in
  let u = unit 2304 in
  let th = c983sa_apply C983IA_CONV spec
    [u; pos; side; south; north; missing4; missing5; missingLow; missingHigh; seg] in
  c983f4f_close (c983sa_stmt [mk_neg (c983f4f_mem 4 7); mk_neg (c983f4f_mem 5 7)]
    (list_mk_conj [c983ab_in 2304 `&49 / &50` `&2`; c983ab_in 2304 `&49 / &50` `&101 / &50`;
                   c983ab_in 2304 `&26 / &25` `&211 / &100`])) th;;

(* Lean: no_inward_impossible (private) *)
let C983IA_NO_INWARD_IMPOSSIBLE =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hh = c983f4f_hh () in
  let noF4 = ASSUME (mk_neg (c983f4f_mem 4 7)) and noF5 = ASSUME (mk_neg (c983f4f_mem 5 7)) in
  let hull = c983f5_use C983IA_MERGED_WEST_HULL [noF4; noF5] in
  let corner = c983f5_use C983IA_NO_MERGED_F5_CORNER [noF5] in
  let marker = seed 8 `&457 / &500` `&2` in
  let [h0; h1; h2] = CONJUNCTS hull in
  let leftAux = MP (SPECL C983E_VARS C983AB_LEFT_AUX) hh in
  let advance = MP (SPECL C983E_VARS C983AB_LEFT_ADVANCE) hh in
  let spec = SPECL (c983ia_trx 4096 `&3` `&2`) OCSCW_IMPOSSIBLE in
  let wall = c983ia_wall 4096 (c983ia_ant spec c983ia_is_forall) in
  let th = c983sa_apply C983IA_CONV spec
    [unit 4096; pos; side; wall; marker; CONJUNCT1 leftAux; advance;
     excl 4096 2304 h0; excl 4096 2304 h1; excl 4096 2304 h2; excl 4096 192 corner] in
  c983f4f_close (c983sa_stmt [mk_neg (c983f4f_mem 4 7); mk_neg (c983f4f_mem 5 7)] `false`) th;;

(* Lean: merged_inward_alternative *)
let C983IA_MERGED_INWARD_ALTERNATIVE =
  let p = c983f4f_mem 4 7 and q = c983f4f_mem 5 7 in
  let f = c983f5_use C983IA_NO_INWARD_IMPOSSIBLE [ASSUME (mk_neg p); ASSUME (mk_neg q)] in
  let pq = mk_disj(p, q) in
  let th = DISJ_CASES (SPEC p EXCLUDED_MIDDLE) (DISJ1 (ASSUME p) q)
             (DISJ_CASES (SPEC q EXCLUDED_MIDDLE) (DISJ2 p (ASSUME q)) (CONTR pq f)) in
  c983f4f_close (c983sa_stmt [] pq) th;;

(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C983/MergedCenterF5.lean.          *)
(* The original merged F5 owner (owners p 7 = owner 2304) has the strict     *)
(* center (2, 2) when 5 IN actual p 7.  Conventions of                       *)
(* CP_OtherCases_C983_F5Filters.ml (owners p 1 = owner 2, owners p 8 =       *)
(* owner 4096).  The Lean proof inside a canonical frame (ClosedFrames.      *)
(* canonical_frame = CLF_CANONICAL_FRAME): positive sector by linear         *)
(* arithmetic, negative sector MergedLeftNegative.point = MLN_POINT; it is   *)
(* packaged as the local geometric lemma C983MCF_POINT.  merged_no_f3 =      *)
(* C983MTE_MERGED_NO_F3, left_aux = C983AB_LEFT_AUX.  Tag C983MCF_.          *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_MergedTopExclusion.ml";;
needs "n12/geometry/CP_OtherCases_C983_F5Filters.ml";;
needs "n12/geometry/MergedLeftNegative.ml";;
needs "n12/geometry/ClosedFrames.ml";;

(* the square argument of f5_merged_center, for an arbitrary square A and left owner L *)
let C983MCF_POINT = prove
 (`forall cA sA uA vA aA cL sL uL vL aL.
     cA * cA + sA * sA = &1 /\ cL * cL + sL * sL = &1 /\ &0 < aL /\
     &1 < aA /\ aA = aL /\ lcont cL sL uL vL aL /\
     linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     linside cA sA uA vA aA (&33 / &20) (&47 / &20) /\
     linside cA sA uA vA aA (&2) (&113 / &50) /\
     ~linside cA sA uA vA aA (&1) (&87 / &50) /\
     ~linside cA sA uA vA aA (&1) (&113 / &50) /\
     ~linside cA sA uA vA aA (&8 / &5) (&3) /\
     linside cL sL uL vL aL (&457 / &500) (&2) /\
     linside cL sL uL vL aL (&1) (&12 / &5) /\
     ldisj cA sA uA vA aA cL sL uL vL aL
     ==> linside cA sA uA vA aA (&2) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check ((=) `aA:real = aL` o concl)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cq:real`; `sq:real`; `uq:real`; `vq:real`; `aq:real`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o check ((=) `aq:real = aA` o concl)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_forall(concl th) && is_iff(snd(strip_forall(concl th)))
     then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) THEN REWRITE_TAC[GSYM th] else NO_TAC)) THEN
  ASM_CASES_TAC `&0 <= sq` THENL
   [MAP_EVERY UNDISCH_TAC
     [`linside cq sq uq vq aA (&33 / &20) (&33 / &20)`;
      `linside cq sq uq vq aA (&33 / &20) (&47 / &20)`;
      `linside cq sq uq vq aA (&2) (&113 / &50)`;
      `abs sq <= cq`; `&0 < cq`; `&0 <= sq`] THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC MLN_POINT THEN
    MAP_EVERY EXISTS_TAC [`cL:real`; `sL:real`; `uL:real`; `vL:real`; `aA:real`] THEN
    ASM_REWRITE_TAC[ldisj] THEN ASM_REAL_ARITH_TAC]);;

(* Lean: f5_merged_center *)
let C983MCF_F5_MERGED_CENTER =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  let hh = c983f4f_hh () in
  let south = seed 7 `&33 / &20` `&33 / &20` and north = seed 7 `&33 / &20` `&47 / &20` in
  let inner = c983f4f_point (c983f5_f5 ()) in
  let lowMissing = excl 2304 2 (seed 1 `&1` `&87 / &50`) in
  let leftAux = MP (SPECL C983E_VARS C983AB_LEFT_AUX) hh in
  let highMissing = excl 2304 4096 (CONJUNCT1 leftAux) in
  let noF3 = MP (SPECL C983E_VARS C983MTE_MERGED_NO_F3) hh in
  let topMissing = PROVE_HYP noF3 (c983sa_missing 3 7) in
  let leftMarker = seed 8 `&457 / &500` `&2` in
  let dj = MP (SPECL C983E_VARS (oo_apart C983E_F 2304 4096)) hh in
  let facts = [unit 2304; unit 4096; pos; side; REFL `l:real`; box 4096; south; north; inner;
               lowMissing; highMissing; topMissing; leftMarker; CONJUNCT2 leftAux; dj] in
  let th = c983sa_apply C983FO_CONV (SPECL (c983ab_own 2304 @ c983ab_own 4096) C983MCF_POINT) facts in
  c983f4f_close (c983sa_stmt [c983f4f_mem 5 7] (c983ab_in 2304 `&2` `&2`)) th;;

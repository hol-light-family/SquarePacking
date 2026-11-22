(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974LocalEnding.lean           *)
(* (N12Compact.Completion.OtherCases.C983.C974LocalEnding).  Full local      *)
(* Theorem 1 of C974-THREE-SQUARE-ENDING and the two actual C983 adapters    *)
(* with their retained singleton seeds (no whole C983 exclusion).            *)
(* Squares K W C are 5-tuples with their OpenSquare invariants explicit;     *)
(* C974LocalData.Input = c983ld_input, C974MissingCorner.Input =             *)
(* c974mc_input (Input.of_local C974MC_INPUT_OF_LOCAL, reframeK/W            *)
(* C974MC_INPUT_REFRAMEK/W), positive_frames C974WS_POSITIVE_FRAMES,         *)
(* reduced_input C974SA_REDUCED_INPUT, C974ReducedEnding.impossible          *)
(* C983RE_IMPOSSIBLE, bottom_input / left_input C983LD_BOTTOM/LEFT_INPUT.    *)
(* family = c983ri_family; owners p 0 / 1 / 2 / 4 / 5 / 8 / 9 = owner        *)
(* 1 / 2 / 12 / 192 / 512 / 4096 / 8192 (see C974LocalData.ml).              *)
(* (Lean header: "source-only and uncompiled".)  Tag C983LE_.                *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974SingletonAngle.ml";;
needs "n12/geometry/CP_OtherCases_C983_C974ReducedEnding.ml";;

(* Lean: impossible *)
let C983LE_IMPOSSIBLE = prove
 (`forall cK sK uK vK aK cW sW uW vW aW cC sC uC vC aC.
     cK * cK + sK * sK = &1 /\ &0 < aK /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cC * cC + sC * sC = &1 /\ &0 < aC /\
     c983ld_input cK sK uK vK aK cW sW uW vW aW cC sC uC vC aC
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP C974MC_INPUT_OF_LOCAL) THEN
  UNDISCH_TAC `c983ld_input cK sK uK vK aK cW sW uW vW aW cC sC uC vC aC` THEN
  REWRITE_TAC[c983ld_input] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C974WS_POSITIVE_FRAMES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `cA:real` (X_CHOOSE_THEN `sA:real` (X_CHOOSE_THEN `uA:real`
    (X_CHOOSE_THEN `vA:real` (X_CHOOSE_THEN `aA:real` (X_CHOOSE_THEN `cB:real`
    (X_CHOOSE_THEN `sB:real` (X_CHOOSE_THEN `uB:real` (X_CHOOSE_THEN `vB:real`
    (X_CHOOSE_THEN `aB:real` STRIP_ASSUME_TAC)))))))))) THEN
  SUBGOAL_THEN `c974mc_input cA sA uA vA aA cW sW uW vW aW` ASSUME_TAC THENL
   [MATCH_MP_TAC C974MC_INPUT_REFRAMEK THEN
    MAP_EVERY EXISTS_TAC [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `c974mc_input cA sA uA vA aA cB sB uB vB aB` ASSUME_TAC THENL
   [MATCH_MP_TAC C974MC_INPUT_REFRAMEW THEN
    MAP_EVERY EXISTS_TAC [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C974SA_REDUCED_INPUT) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC]) THEN
  MATCH_MP_TAC (SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                       `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                       `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C983RE_IMPOSSIBLE) THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         RASM_ARITH_TAC;
         UNDISCH_TAC `ldisj cW sW uW vW aW cC sC uC vC aC` THEN
         REWRITE_TAC[ldisj] THEN ASM_REWRITE_TAC[]]);;

(* apply C983LE_IMPOSSIBLE to three owner tuples given the Input theorem *)
let C983LE_CLOSE_TAC inth tK tW tC (asl, w as gl) =
  let side, pos, unit, box, seed, apart, excl = c983fo_facts () in
  (MATCH_MP_TAC (SPECL (tK @ tW @ tC) C983LE_IMPOSSIBLE) THEN
   REPEAT CONJ_TAC THENL
    [MP_TAC(unit 1) THEN MP_TAC(unit 2) THEN MP_TAC(unit 12) THEN
     MP_TAC(unit 192) THEN MP_TAC(unit 4096) THEN MP_TAC(unit 8192) THEN REAL_ARITH_TAC;
     ACCEPT_TAC pos;
     MP_TAC(unit 1) THEN MP_TAC(unit 2) THEN MP_TAC(unit 12) THEN
     MP_TAC(unit 192) THEN MP_TAC(unit 4096) THEN MP_TAC(unit 8192) THEN REAL_ARITH_TAC;
     ACCEPT_TAC pos;
     MP_TAC(unit 1) THEN MP_TAC(unit 2) THEN MP_TAC(unit 12) THEN
     MP_TAC(unit 192) THEN MP_TAC(unit 4096) THEN MP_TAC(unit 8192) THEN REAL_ARITH_TAC;
     ACCEPT_TAC pos;
     MP_TAC(SPECL C983E_VARS inth) THEN ASM_REWRITE_TAC[]]) gl;;

(* Lean: bottom_missing_corner_excluded_of_seeds *)
let C983LE_BOTTOM_MISSING_CORNER_EXCLUDED_OF_SEEDS =
  let hyps = [mk_neg (c983ab_in 1 `&1` `&1`); c983ab_in 1 `&91 / &50` `&1`;
              c983ab_in 1 `&49 / &25` `&19 / &25`; c983ab_in 8192 `&2` `&1`;
              mk_neg (c983ab_in 8192 `&2` `&3 / &2`); c983ab_in 512 `&3` `&3 / &2`] in
  prove
   (c983sa_stmt hyps `false`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    C983LE_CLOSE_TAC C983LD_BOTTOM_INPUT (c983ld_tr (c983ab_own 1))
      (c983ld_tr (c983ab_own 8192)) (c983ld_tr (c983ab_own 12)));;

(* Lean: left_missing_corner_excluded_of_seeds *)
let C983LE_LEFT_MISSING_CORNER_EXCLUDED_OF_SEEDS =
  let hyps = [c983f4f_mem 4 7; mk_neg (c983ab_in 2 `&1` `&1`); c983ab_in 2 `&1` `&91 / &50`;
              c983ab_in 2 `&19 / &25` `&49 / &25`] in
  let tr t = c983ld_tr (c983ld_sw t) in
  prove
   (c983sa_stmt hyps `false`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    C983LE_CLOSE_TAC C983LD_LEFT_INPUT (tr (c983ab_own 2)) (tr (c983ab_own 4096))
      (tr (c983ab_own 192)));;

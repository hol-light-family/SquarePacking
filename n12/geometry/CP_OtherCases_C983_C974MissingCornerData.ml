(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974MissingCornerData.lean     *)
(* (N12Compact.Completion.OtherCases.C983.C974MissingCorner).  Point/face    *)
(* reductions of MISSING-CORNER-WALL-SIGN / MISSING-CORNER-MIDPOINT.         *)
(* Input K W is c974mc_input (K) (W) over two 5-tuples (the OpenSquare       *)
(* invariants c*c+s*s=1, 0<a are explicit hypotheses where used); apart is   *)
(* ldisj.  C974LocalData.Input = c983ld_input; ClosedFrames.canonical_frame  *)
(* = CLF_CANONICAL_FRAME; turnFrame (c,s,u,v,a) = (--s,c,v,--u-a,a);         *)
(* affine_endpoint_nonnegative = SCAP_AFFINE_ENDPOINT_NONNEG.                *)
(* (Lean header: "this module has not been replayed".)  Tag C974MC_.        *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974LocalData.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/SectionCapacity.ml";;

(* Lean: Input *)
let c974mc_input = new_definition
 `c974mc_input (cK:real) (sK:real) (uK:real) (vK:real) (aK:real)
               (cW:real) (sW:real) (uW:real) (vW:real) (aW:real) <=>
    &1 < aK /\ aK = aW /\
    (forall x y. linside cK sK uK vK aK x y ==> --(&1) <= y) /\
    linside cK sK uK vK aK (&0) (--(&43 / &500)) /\
    linside cK sK uK vK aK (&41 / &50) (&0) /\
    linside cK sK uK vK aK (&24 / &25) (--(&6 / &25)) /\
    ~linside cK sK uK vK aK (&0) (&0) /\
    linside cW sW uW vW aW (&1) (&0) /\
    linside cW sW uW vW aW (&1) (--(&43 / &500)) /\
    linside cW sW uW vW aW (&9 / &5) (&0) /\
    ~linside cW sW uW vW aW (&27 / &20) (&13 / &20) /\
    ~linside cW sW uW vW aW (&2) (&0) /\
    ~linside cW sW uW vW aW (&1) (&1 / &2) /\
    ~linside cW sW uW vW aW (&2) (&1 / &2) /\
    ldisj cK sK uK vK aK cW sW uW vW aW`;;

(* Lean: Input.of_local *)
let C974MC_INPUT_OF_LOCAL = prove
 (`forall cK sK uK vK aK cW sW uW vW aW cC sC uC vC (aC:real).
     c983ld_input cK sK uK vK aK cW sW uW vW aW cC sC uC vC aC
     ==> c974mc_input cK sK uK vK aK cW sW uW vW aW`,
  REWRITE_TAC[c983ld_input; c974mc_input; ldisj] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: Input.reframeK *)
let C974MC_INPUT_REFRAMEK = prove
 (`forall cK sK uK vK aK cW sW uW vW aW cR sR uR vR aR.
     c974mc_input cK sK uK vK aK cW sW uW vW aW /\ aR = aK /\
     (forall x y. linside cR sR uR vR aR x y <=> linside cK sK uK vK aK x y)
     ==> c974mc_input cR sR uR vR aR cW sW uW vW aW`,
  REWRITE_TAC[c974mc_input; ldisj] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: Input.reframeW *)
let C974MC_INPUT_REFRAMEW = prove
 (`forall cK sK uK vK aK cW sW uW vW aW cR sR uR vR aR.
     c974mc_input cK sK uK vK aK cW sW uW vW aW /\ aR = aW /\
     (forall x y. linside cR sR uR vR aR x y <=> linside cW sW uW vW aW x y)
     ==> c974mc_input cK sK uK vK aK cR sR uR vR aR`,
  REWRITE_TAC[c974mc_input; ldisj] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* closes a goal by contradiction with a negated (unfolded) point assumption *)
let C974MC_NEG_TAC =
  FIRST_X_ASSUM(fun th -> if is_neg (concl th) then
    MP_TAC th THEN REWRITE_TAC[] THEN RASM_ARITH_TAC else NO_TAC);;

let C974MC_LIN = NLIN_TAC ~deg2:false [];;
(* open the Input, unfolding only the positive point facts *)
let C974MC_OPEN_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if is_comb (concl th) && fst (strip_comb (concl th)) = `c974mc_input`
    then STRIP_ASSUME_TAC (REWRITE_RULE[c974mc_input] th) else NO_TAC) THEN
  RULE_ASSUM_TAC(fun th -> let t = concl th in
    if is_comb t && fst (strip_comb t) = `linside` then
      CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) (REWRITE_RULE[linside] th) else th);;
(* contradiction with the missing point tm *)
let C974MC_MISS_TAC tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[linside; TAUT `~p ==> false <=> p`] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REPEAT CONJ_TAC THEN C974MC_LIN;;
let C974MC_FACT t tac = SUBGOAL_THEN t ASSUME_TAC THENL [tac; ALL_TAC];;
let C974MC_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

(* Lean: singleton_positive_cap *)
let C974MC_SINGLETON_POSITIVE_CAP = prove
 (`forall cK sK uK vK aK cW sW uW vW (aW:real).
     c974mc_input cK sK uK vK aK cW sW uW vW aW /\ &0 < cK /\ &0 <= sK
     ==> &0 < sK /\ vK + aK <= &0`,
  REWRITE_TAC[c974mc_input; linside] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `vK + aK <= &0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    C974MC_NEG_TAC;
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]);;

(* Lean: singleton_negative_cap *)
let C974MC_SINGLETON_NEGATIVE_CAP = prove
 (`forall cK sK uK vK aK cW sW uW vW (aW:real).
     c974mc_input cK sK uK vK aK cW sW uW vW aW /\ &0 < cK /\ sK <= &0
     ==> sK < &0 /\ &0 <= uK`,
  REWRITE_TAC[c974mc_input; linside] THEN
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= uK` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    C974MC_NEG_TAC;
    ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]);;

(* Lean: singleton_quadrant *)
let C974MC_SINGLETON_QUADRANT = prove
 (`forall cK sK uK vK aK cW sW uW vW aW.
     cK * cK + sK * sK = &1 /\ &0 < aK /\ c974mc_input cK sK uK vK aK cW sW uW vW aW
     ==> exists cR sR uR vR aR. cR * cR + sR * sR = &1 /\ &0 < aR /\ aR = aK /\
           (forall x y. linside cR sR uR vR aR x y <=> linside cK sK uK vK aK x y) /\
           &0 < cR /\ &0 < sR /\ vR + aR <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `c974mc_input cR sR uR vR aR cW sW uW vW aW` ASSUME_TAC THENL
   [MATCH_MP_TAC C974MC_INPUT_REFRAMEK THEN
    MAP_EVERY EXISTS_TAC [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= sR` THENL
   [MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
           C974MC_SINGLETON_POSITIVE_CAP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`]
           C974MC_SINGLETON_NEGATIVE_CAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    MAP_EVERY EXISTS_TAC [`--sR:real`; `cR:real`; `vR:real`; `--uR - aR:real`; `aR:real`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if is_forall (concl th) &&
      can (find_term ((=) `linside`)) (concl th) &&
      can (find_term ((=) `cR:real`)) (concl th) then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN TRY(REPEAT GEN_TAC THEN REAL_ARITH_TAC) THEN
    TRY(UNDISCH_TAC `cR * cR + sR * sR = &1` THEN REAL_ARITH_TAC) THEN ASM_REAL_ARITH_TAC]);;

(* Lean: singleton_wall *)
let C974MC_SINGLETON_WALL = prove
 (`forall cK sK uK vK aK cW sW uW vW aW.
     cK * cK + sK * sK = &1 /\ c974mc_input cK sK uK vK aK cW sW uW vW aW
     ==> aK * cK - &1 <= sK * uK + cK * (vK + aK)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c974mc_input] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &1 + sK * uK + cK * vK` MP_TAC THENL
   [MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
    MAP_EVERY EXISTS_TAC [`aK:real`; `sK + cK:real`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`cK * (uK + t) - sK * (vK + t)`; `sK * (uK + t) + cK * (vK + t)`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[linside] THEN
      SUBGOAL_THEN `cK * (cK * (uK + t) - sK * (vK + t)) + sK * (sK * (uK + t) + cK * (vK + t)) =
                    (cK * cK + sK * sK) * (uK + t) /\
                    --sK * (cK * (uK + t) - sK * (vK + t)) + cK * (sK * (uK + t) + cK * (vK + t)) =
                    (cK * cK + sK * sK) * (vK + t)` (fun th -> REWRITE_TAC[th]) THENL
       [REAL_ARITH_TAC; ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* Lean: wall_positive_caps *)
let C974MC_WALL_POSITIVE_CAPS = prove
 (`forall cK sK uK vK aK cW sW uW vW aW.
     cW * cW + sW * sW = &1 /\ c974mc_input cK sK uK vK aK cW sW uW vW aW /\
     &0 < cW /\ &0 <= sW /\ sW <= cW
     ==> uW + aW <= &2 * cW /\ vW + aW <= cW / &2 - sW`,
  C974MC_OPEN_TAC THEN
  C974MC_FACT `vW + aW <= cW / &2 - sW`
    (C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW sW uW vW aW (&1) (&1 / &2)`) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `uW + aW <= &2 * cW` THEN ASM_REWRITE_TAC[] THEN
  C974MC_FACT `--(&2 * sW) <= vW`
    (C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW sW uW vW aW (&2) (&0)`) THEN
  ASM_CASES_TAC `uW + aW <= &27 / &20 * cW + &13 / &20 * sW` THENL
   [C974MC_LIN; ALL_TAC] THEN
  C974MC_FACT `vW + aW <= --(&27 / &20 * sW) + &13 / &20 * cW`
    (C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW sW uW vW aW (&27 / &20) (&13 / &20)`) THEN
  C974MC_FACT `cW + sW <= &3 / &2` (NLIN_TAC [SQ_NONNEG `cW - sW:real`]) THEN
  C974MC_LIN);;

(* Lean: wall_positive_slope *)
let C974MC_WALL_POSITIVE_SLOPE = prove
 (`forall cK sK uK vK aK cW sW uW vW aW.
     cW * cW + sW * sW = &1 /\ c974mc_input cK sK uK vK aK cW sW uW vW aW /\
     &0 < cW /\ &0 <= sW /\ sW <= cW
     ==> &3 * sW < &2 * cW`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C974MC_WALL_POSITIVE_CAPS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cW sW uW vW aW (&24 / &25) (--(&6 / &25))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c974mc_input; ldisj] o
      check (fun th -> is_comb (concl th) && fst (strip_comb (concl th)) = `c974mc_input`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN C974MC_OPEN_TAC THEN
  C974MC_FACT `cW <= &1` (NLIN_TAC [SQ_NONNEG `sW:real`]) THEN
  C974MC_FACT `&24 / &25 * cW - &6 / &25 * sW <= uW`
    (C974MC_CONTRA THEN C974MC_MISS_TAC `~linside cW sW uW vW aW (&24 / &25) (--(&6 / &25))`) THEN
  C974MC_FACT `&1 < &26 / &25 * cW + &6 / &25 * sW` C974MC_LIN THEN
  C974MC_CONTRA THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&3 * sW - &2 * cW) * (&2544 / &625 * sW + &344 / &625 * cW)`;
    `&0 < (&26 / &25 * cW + &6 / &25 * sW - &1) * (&26 / &25 * cW + &6 / &25 * sW + &1)`] THEN
  NLIN_TAC []);;

(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalCenteredCaps.lean         *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  Face producers shared by    *)
(* the centered negative cap and angle chapters.  A single square is         *)
(* c s u v a; the pair C, E is cC .., cE ...  Normal: c977cc_normal;         *)
(* short_projections: WFP_SHORT_PROJECTIONS; InwardCenterDiagonal.long_point:*)
(* C1092ICD_LONG_POINT; opposite q is (c, s, --u - a, --v - a, a)            *)
(* (C1092IFCC_OPPOSITE); NegativeSuccessor: c1092ifsu_negsucc; half /       *)
(* quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA; half_cross:          *)
(* C1092MIFE_HALF_CROSS; CanonicalProjection.before: CCCP_BEFORE.            *)
(* PredecessorPoints: c1092ifcc_predecessorPoints.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalBarProfile.ml";;
needs "n12/geometry/CP_C1092_InwardCenterDiagonal.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalEndpoints.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/WallForcedPoint.ml";;

let C1092IFCC_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;

let C1092IFCC_TRANSFER_TAC =
  FIRST_ASSUM ACCEPT_TAC ORELSE
  FIRST_ASSUM(fun th ->
    let t = concl th in let t = if is_neg t then rand t else t in
    if can (term_match [] `linside c s u v a x y`) t
    then MP_TAC th THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC else NO_TAC);;

let C1092IFCC_SP_TAC dx dy =
  MP_TAC(SPECL [`c:real`; `s:real`; dx; dy] WFP_SHORT_PROJECTIONS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; STRIP_TAC];;

(* Lean: inside_opposite *)
let C1092IFCC_OPPOSITE = prove
 (`forall c s u v a x y.
     linside c s (--u - a) (--v - a) a x y <=> linside c s u v a (--x) (--y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: centered_marker_caps *)
let C1092IFCC_CENTERED_MARKER_CAPS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\
     linside c s u v a (&0) (&0) /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20)
     ==> u + a <= (&7 / &20) * (c - s) /\ v + a <= (&7 / &20) * (c + s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN C1092IFBP_OPEN_TAC THEN
  C1092IFCC_SP_TAC `&7 / &10` `--(&7 / &10)` THEN
  SUBGOAL_THEN `u + a <= (&7 / &20) * (c - s)` ASSUME_TAC THENL
   [C1092IFBP_MISS_TAC `~linside c s u v a (&7 / &20) (--(&7 / &20))`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092IFBP_MISS_TAC `~linside c s u v a (--(&7 / &20)) (&7 / &20)`);;

(* Lean: centered_lower_face *)
let C1092IFCC_CENTERED_LOWER_FACE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     linside c s u v a (&0) (--(&13 / &50)) /\
     v + a <= (&7 / &20) * (c + s) /\
     ~(linside c s u v a (--(&1)) (--(&13 / &50)) /\
       linside c s u v a (--(&1)) (--(&2 / &5)))
     ==> --c - (&13 / &50) * s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  ASM_CASES_TAC `linside c s u v a (--(&1)) (--(&2 / &5))` THENL
   [SUBGOAL_THEN `~linside c s u v a (--(&1)) (--(&13 / &50))` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    C1092IFBP_OPEN_TAC THEN
    C1092IFBP_MISS_TAC `~linside c s u v a (--(&1)) (--(&13 / &50))`;
    C1092IFBP_OPEN_TAC THEN C1092IFCC_SP_TAC `&3 / &4` `--(&13 / &20)` THEN
    SUBGOAL_THEN `--c - (&2 / &5) * s <= u` ASSUME_TAC THENL
     [C1092IFBP_MISS_TAC `~linside c s u v a (--(&1)) (--(&2 / &5))`; ALL_TAC] THEN
    RASM_ARITH_TAC]);;

(* Lean: successor_sharp *)
let C1092IFCC_SUCCESSOR_SHARP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c1092ifsu_negsucc c s u v a
     ==> linside c s u v a (&7 / &50) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092ifsu_negsucc] THEN STRIP_TAC THEN
  C1092IFCC_SP_TAC `&43 / &50` `--(&1 / &2)` THEN
  C1092IFCC_SP_TAC `&7 / &50` `--(&6 / &25)` THEN
  C1092IFCC_SP_TAC `&43 / &50` `&1 / &10` THEN
  C1092IFCC_SP_TAC `&7 / &50` `&293 / &500` THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: centered_first_cap *)
let C1092IFCC_CENTERED_FIRST_CAP = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c977cc_normal cC (--sC) /\
     linside cC sC uC vC aC (&0) (&0) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (&7 / &20) (--(&7 / &20)) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20) /\
     c1092ifsu_negsucc cE sE uE vE aE /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> uC + aC <= (&7 / &50) * cC - sC / &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `--uC - aC`; `--vC - aC`; `aC:real`] C1092ICD_LONG_POINT) THEN
  REWRITE_TAC[C1092IFCC_OPPOSITE] THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN C1092IFCC_TRANSFER_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092IFCC_SUCCESSOR_SHARP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  C1092PRS_NORMAL_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&7 / &50`; `--(&1 / &2)`] o check (is_forall o concl)) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
    check (can (term_match [] `linside cC sC uC vC aC x y`) o concl))) THEN
  REWRITE_TAC[linside] THEN C1092IFCC_LIN);;

(* Lean: PredecessorPoints (structure) *)
let c1092ifcc_predecessorPoints = new_definition
 `c1092ifcc_predecessorPoints (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    linside c s u v a (--(&7 / &20)) (&7 / &20) /\
    linside c s u v a (--(&13 / &50)) (&1) /\
    linside c s u v a (--(&2 / &5)) (&1) /\
    ~linside c s u v a (&0) (&543 / &500) /\
    ~linside c s u v a (--(&1)) (&1) /\
    ~linside c s u v a (--(&1)) (&543 / &500)`;;

(* Lean: nonpositive_predecessor_faces *)
let C1092IFCC_NONPOSITIVE_PREDECESSOR_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\
     c1092ifcc_predecessorPoints c s u v a
     ==> --c + s <= u /\ v + a <= (&543 / &500) * c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092ifcc_predecessorPoints] THEN STRIP_TAC THEN
  C1092PRS_NORMAL_TAC THEN C1092IFBP_OPEN_TAC THEN
  SUBGOAL_THEN `--c + s <= u` ASSUME_TAC THENL
   [C1092IFBP_MISS_TAC `~linside c s u v a (--(&1)) (&1)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  C1092IFBP_MISS_TAC `~linside c s u v a (&0) (&543 / &500)`);;

let C1092IFCC_ENDPOINT = prove
 (`c977cc_normal (&248151 / &251849) (&43000 / &251849) /\
   C1092WPS_half (&248151 / &251849) (&43000 / &251849) = &43 / &500`,
  REWRITE_TAC[c977cc_normal; C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* the half-angle bound from a long face sum (local) *)
let C1092IFCC_SMALL_HALF = prove
 (`forall c s. c977cc_normal c s /\ &1 < c + (&43 / &500) * s
     ==> C1092WPS_half c s < &43 / &500 /\ c + s < &29 / &25`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092PRS_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half c s < &43 / &500` ASSUME_TAC THENL
   [ABBREV_TAC `z = C1092WPS_half c s` THEN
    ASSUME_TAC(SPEC `z:real` REAL_LE_POW_2) THEN
    SUBGOAL_THEN `(&1 + z pow 2) * (c + &43 / &500 * s - &1) = &2 * z * (&43 / &500 - z)`
      ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(&1 + z pow 2) * c = &1 - z pow 2`;
                             `(&1 + z pow 2) * s = &2 * z`] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    C1092PRS_PROD `&0 < (&1 + z pow 2) * (c + &43 / &500 * s - &1)` THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    C1092PRS_PROD `&0 <= (&2 * z) * (z - &43 / &500)` THEN NLIN_TAC ~deg2:false [];
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&248151 / &251849`; `&43000 / &251849`]
    C1092MIFE_HALF_CROSS) THEN
  REWRITE_TAC[C1092IFCC_ENDPOINT] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `&248151 / &251849`; `&43000 / &251849`; `&1`; `&1`]
    CCCP_BEFORE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN RASM_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

(* Lean: nonnegative_predecessor_faces *)
let C1092IFCC_NONNEGATIVE_PREDECESSOR_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c s /\
     c1092ifcc_predecessorPoints c s u v a
     ==> v + a <= (&543 / &500) * c + s /\
         (v + a <= (&543 / &500) * c \/
          (u + a <= (&543 / &500) * s /\
           (v + a <= c + s \/
            (--c + s <= u /\ C1092WPS_half c s < &43 / &500 /\ c + s < &29 / &25))))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092ifcc_predecessorPoints] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092IFCC_SMALL_HALF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  C1092PRS_NORMAL_TAC THEN C1092IFBP_OPEN_TAC THEN
  ASM_CASES_TAC `v + a <= (&543 / &500) * c` THENL
   [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= (&543 / &500) * s` ASSUME_TAC THENL
   [C1092IFBP_MISS_TAC `~linside c s u v a (&0) (&543 / &500)`; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&543 / &500) * c + s` ASSUME_TAC THENL
   [C1092IFBP_MISS_TAC `~linside c s u v a (--(&1)) (&543 / &500)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `v + a <= c + s` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `--c + s <= u` ASSUME_TAC THENL
   [C1092IFBP_MISS_TAC `~linside c s u v a (--(&1)) (&1)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN RASM_ARITH_TAC);;

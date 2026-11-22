(* ========================================================================= *)
(* Port of Compact/Completion/FiniteCases/TopMergedInward.lean               *)
(* (N12Compact.FiniteCases.TopMergedInward).  One all-orientation ending for *)
(* the merged NW/top owner's incoming F5 alternative.                        *)
(* Squares h, n, r are (cH, ..), (cN, ..), (cR, ..); apart is ldisj;          *)
(* InsideContainer is lcont.  The square (Transform true true false).pull n  *)
(* = pullSwap (pullX n) is (sN, --cN, uN - 4 cN, vN + 4 sN, aN)              *)
(* (FCTMI_TURN); pullSwap / pullX: LINSIDE_PULLSW / LINSIDE_PULLX.           *)
(* The checked TriangleCertificate commonTriangle and S12.inside_segment are *)
(* replaced by the explicit convex combinations they certify (linear         *)
(* arithmetic on the face inequalities).                                     *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_CommonCases_OutwardPoint.ml";;
needs "n12/geometry/CP_FiniteCases_WallHighFromMarker.ml";;
needs "n12/geometry/CP_FiniteCases_TopElbowCompletion.ml";;
needs "n12/geometry/CP_C981_UpperPoint.ml";;

let FCTMI_TURN = prove
 (`forall c s u v a x y.
     linside s (--c) (u - &4 * c) (v + &4 * s) a x y <=> linside c s u v a (&4 - y) x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* the instances of ldisj at the listed points, as assumptions *)
let FCTMI_APART_TAC pts =
  FIRST_ASSUM(fun th -> if can (term_match [] `ldisj c s u v a c' s' u' v' a'`) (concl th)
    then MAP_EVERY (fun (x,y) -> ASSUME_TAC(SPECL [x; y] (REWRITE_RULE[ldisj] th))) pts
    else NO_TAC);;

let FCTMI_HYPS_TAC =
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  (fun g -> if is_forall(snd g) || is_neg(snd g) then ASM_MESON_TAC[] g
            else ASM_REAL_ARITH_TAC g);;

(* Lean: commonTriangle / triangle_checked (private): the certified point   *)
(* (199/100,123/50) is a convex combination of the three owned points       *)
let FCTMI_COMMON_TRIANGLE = prove
 (`forall c s u v a.
     linside c s u v a (&2) (&113 / &50) /\ linside c s u v a (&2) (&1543 / &500) /\
     linside c s u v a (&33 / &20) (&47 / &20)
     ==> linside c s u v a (&199 / &100) (&123 / &50)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let FCTMI_IMPOSSIBLE = prove
 (`forall cH sH uH vH aH cN sN uN vN aN.
     cH * cH + sH * sH = &1 /\ &0 < aH /\ cN * cN + sN * sN = &1 /\ &1 < aN /\
     linside cH sH uH vH aH (&33 / &20) (&47 / &20) /\
     linside cH sH uH vH aH (&2) (&1543 / &500) /\
     linside cH sH uH vH aH (&2) (&113 / &50) /\
     linside cN sN uN vN aN (&47 / &20) (&47 / &20) /\
     linside cN sN uN vN aN (&12 / &5) (&3) /\
     (linside cN sN uN vN aN (&113 / &50) (&2) \/ linside cN sN uN vN aN (&113 / &50) (&3)) /\
     ~linside cN sN uN vN aN (&3) (&3) /\
     ~linside cN sN uN vN aN (&3) (&1543 / &500) /\
     (forall z. &113 / &50 <= z ==> z <= &14 / &5 ==> ~linside cN sN uN vN aN (&3) z) /\
     ldisj cH sH uH vH aH cN sN uN vN aN
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FCTMI_APART_TAC [`&2`,`&113 / &50`; `&2`,`&1543 / &500`; `&199 / &100`,`&123 / &50`] THEN
  MP_TAC(SPECL [`cH:real`; `sH:real`; `uH:real`; `vH:real`; `aH:real`] FCTMI_COMMON_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~linside cN sN uN vN aN (&2) (&113 / &50) /\
                ~linside cN sN uN vN aN (&2) (&1543 / &500) /\
                ~linside cN sN uN vN aN (&199 / &100) (&123 / &50)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cN sN uN vN aN (&113 / &50) (&2)` ASSUME_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC C981OA_IMPOSSIBLE THEN
    MAP_EVERY EXISTS_TAC [`sN:real`; `--cN`; `uN - &4 * cN`; `vN + &4 * sN`; `aN:real`] THEN
    REWRITE_TAC[FCTMI_TURN] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    FCTMI_HYPS_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&113 / &50) (&3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&199 / &100) (&123 / &50)` MP_TAC THENL
   [ONCE_REWRITE_TAC[GSYM LINSIDE_PULLSW] THEN MATCH_MP_TAC CCOP_POINT_ORIGINAL THEN
    REWRITE_TAC[LINSIDE_PULLSW] THEN FCTMI_HYPS_TAC;
    ASM_REWRITE_TAC[]]);;

(* Lean: short_impossible *)
let FCTMI_SHORT_IMPOSSIBLE = prove
 (`forall cH sH uH vH aH cN sN uN vN aN cR sR uR vR aR.
     cH * cH + sH * sH = &1 /\ &0 < aH /\ cN * cN + sN * sN = &1 /\ &1 < aN /\
     cR * cR + sR * sR = &1 /\ &1 < aR /\ lcont cR sR uR vR aR /\
     linside cH sH uH vH aH (&2) (&1543 / &500) /\
     linside cH sH uH vH aH (&2) (&113 / &50) /\
     linside cN sN uN vN aN (&47 / &20) (&47 / &20) /\
     linside cN sN uN vN aN (&12 / &5) (&3) /\
     (linside cN sN uN vN aN (&113 / &50) (&2) \/ linside cN sN uN vN aN (&113 / &50) (&3)) /\
     ~linside cN sN uN vN aN (&3) (&3) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     ~linside cR sR uR vR aR (&3) (&87 / &50) /\
     ldisj cH sH uH vH aH cN sN uN vN aN /\
     ldisj cN sN uN vN aN cR sR uR vR aR
     ==> false`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `linside cH sH uH vH aH (&2) (&12 / &5) /\ linside cH sH uH vH aH (&2) (&3) /\
                linside cH sH uH vH aH (&2) (&131 / &50)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `linside cH sH uH vH aH (&2) (&1543 / &500)` THEN
    UNDISCH_TAC `linside cH sH uH vH aH (&2) (&113 / &50)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN
  SUBGOAL_THEN `~linside cN sN uN vN aN (&2) (&12 / &5) /\ ~linside cN sN uN vN aN (&2) (&3) /\
                ~linside cN sN uN vN aN (&2) (&131 / &50) /\
                ~linside cN sN uN vN aN (&3) (&12 / &5) /\
                ~linside cR sR uR vR aR (&47 / &20) (&47 / &20)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&113 / &50) (&3)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FCTEC_POINT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linside cR sR uR vR aR (&3) (&64 / &25)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`--cR`; `sR:real`; `uR - &4 * cR`; `--vR - aR - &4 * sR`; `aR:real`]
      FCWHM_POINT) THEN
    REWRITE_TAC[LINSIDE_PULLX] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[LCONT_PULLX] THEN FCTMI_HYPS_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~linside cN sN uN vN aN (&3) (&64 / &25)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `linside cN sN uN vN aN (&2) (&131 / &50)` MP_TAC THENL
   [MATCH_MP_TAC C981UP_POINT THEN FCTMI_HYPS_TAC; ASM_REWRITE_TAC[]]);;

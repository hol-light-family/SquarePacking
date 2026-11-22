(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalEndpoints.lean            *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  Exact rational successor    *)
(* endpoints of the two inward-final chapters.  Normal: c977cc_normal;       *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;               *)
(* FE / alpha: c1092mifss_FE / c1092mifss_alpha.                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessorScalars.ml";;

(* Lean: powers (private) *)
let C1092MIFE_POWERS = prove
 (`forall x a. &0 <= x /\ x <= a
         ==> x pow 2 <= a pow 2 /\ x pow 3 <= a pow 3 /\ x pow 4 <= a pow 4`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_POW_LE2 THEN ASM_REWRITE_TAC[]);;

(* the half-angle data of a Normal, with x = half c s *)
let C1092MIFE_HALF_TAC c s x =
  MP_TAC(SPECL [c; s] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(x, list_mk_comb(`C1092WPS_half`,[c; s]))) THEN STRIP_TAC;;

(* Lean: rational_frame (private) *)
let C1092MIFE_RATIONAL_FRAME = prove
 (`forall c s. c977cc_normal c s
     ==> c = (&1 - C1092WPS_half c s pow 2) / (&1 + C1092WPS_half c s pow 2) /\
         s = (&2 * C1092WPS_half c s) / (&1 + C1092WPS_half c s pow 2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFE_HALF_TAC `c:real` `s:real` `x:real` THEN
  SUBGOAL_THEN `&0 < &1 + x pow 2` ASSUME_TAC THENL
   [MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_EQ_RDIV_EQ] THEN
  CONJ_TAC THEN RASM_ARITH_TAC);;

(* Lean: half_cross *)
let C1092MIFE_HALF_CROSS = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             C1092WPS_half c s <= C1092WPS_half d t
     ==> s * d <= c * t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFE_HALF_TAC `c:real` `s:real` `x:real` THEN
  C1092MIFE_HALF_TAC `d:real` `t:real` `y:real` THEN
  SUBGOAL_THEN `(&1 + x pow 2) * (&1 + y pow 2) * (c * t - s * d) =
                &2 * (y - x) * (&1 + x * y)` ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN
    UNDISCH_TAC `(&1 + y pow 2) * d = &1 - y pow 2` THEN
    UNDISCH_TAC `(&1 + y pow 2) * t = &2 * y` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  NLIN_FACTS_TAC []
   [`&0 <= x * y`; `&0 <= &2 * (y - x) * (&1 + x * y)`;
    `&0 < (&1 + x * x) * (&1 + y * y)`] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`((&1 + x * x) * (&1 + y * y)) * (c * t - s * d) < &0`] THEN
  RASM_ARITH_TAC);;

(* 0 < FE ... from K (1 + x^2)^2 FE = poly(x) and poly(x) > 0 on [0,a] *)
let C1092MIFE_ENDPOINT_TAC fe k poly a =
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MIFS_NORMAL_TAC THEN
  C1092MIFE_HALF_TAC `c:real` `s:real` `x:real` THEN
  let lhs = mk_comb(mk_comb(`( * ):real->real->real`,
              mk_comb(mk_comb(`( * ):real->real->real`,k),`(&1 + x pow 2) pow 2`)),fe) in
  SUBGOAL_THEN (mk_eq(lhs,poly)) ASSUME_TAC THENL
   [REWRITE_TAC[c1092mifss_FE; c1092mifss_alpha] THEN
    UNDISCH_TAC `(&1 + x pow 2) * c = &1 - x pow 2` THEN
    UNDISCH_TAC `(&1 + x pow 2) * s = &2 * x` THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real`; a] C1092MIFE_POWERS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(SPEC `x:real` REAL_LE_POW_2) THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):real->real->bool`,`&0`),poly)) ASSUME_TAC THENL
   [RULE_ASSUM_TAC(CONV_RULE(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV)) THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN (mk_comb(mk_comb(`(<):real->real->bool`,`&0`),
     mk_comb(mk_comb(`( * ):real->real->real`,k),`(&1 + x pow 2) pow 2`))) ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_POW_LT THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [mk_comb(mk_comb(`( * ):real->real->real`,k),`(&1 + x pow 2) pow 2`);
                mk_comb(`(--):real->real`,fe)] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC;;

(* Lean: centered_half_endpoint *)
let C1092MIFE_CENTERED_HALF_ENDPOINT = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &91 / &1000
     ==> &0 < c1092mifss_FE (&1 / &2) (c / &11 - s / &2) c s
                (&95727000 / &103958161) (&40541839 / &103958161)`,
  C1092MIFE_ENDPOINT_TAC
    `c1092mifss_FE (&1 / &2) (c / &11 - s / &2) c s
       (&95727000 / &103958161) (&40541839 / &103958161)`
    `&1143539771`
    `&50000932 - &415582771 * x + &262169220 * x pow 2 - &2012564313 * x pow 3 -
     &2947913526 * x pow 4`
    `&91 / &1000`);;

(* Lean: centered_final_endpoint *)
let C1092MIFE_CENTERED_FINAL_ENDPOINT = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &91 / &1000
     ==> &0 < c1092mifss_FE (&13 / &50) (c / &11 - s / &2) c s (&4165 / &4813) (&2412 / &4813)`,
  C1092MIFE_ENDPOINT_TAC
    `c1092mifss_FE (&13 / &50) (c / &11 - s / &2) c s (&4165 / &4813) (&2412 / &4813)`
    `&1323575`
    `&117900 - &823605 * x - &159768 * x pow 2 - &1104695 * x pow 3 - &3499450 * x pow 4`
    `&91 / &1000`);;

(* Lean: missing_final_endpoint *)
let C1092MIFE_MISSING_FINAL_ENDPOINT = prove
 (`forall c s. c977cc_normal c s /\ C1092WPS_half c s <= &1 / &10
     ==> &0 < c1092mifss_FE (&13 / &50) (&0) c s (&4165 / &4813) (&2412 / &4813)`,
  C1092MIFE_ENDPOINT_TAC
    `c1092mifss_FE (&13 / &50) (&0) c s (&4165 / &4813) (&2412 / &4813)`
    `&120325`
    `-- &312650 * x pow 4 - &21195 * x pow 3 + &182762 * x pow 2 - &154105 * x + &16200`
    `&1 / &10`);;

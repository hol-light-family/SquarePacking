(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualBoundaryOrigin.lean            *)
(* (N12Compact.C1092MPPMActualBoundaryOrigin; Lean header: "Source only,     *)
(* uncompiled").  Actual positive-predecessor production under a missing Q9 *)
(* origin.  Conventions of CP_C1092_MPPMPositiveOverlap.ml: owners p i at    *)
(* mask EL i c1092wc_code, side l; Ordinary p is c1092mpapo_ordinary;        *)
(* ActualFrame p C is c1092psa_frame; OpenSquares C, B, L are 5-tuples with  *)
(* their invariants as hypotheses; Normal is c977cc_normal.  PositiveSource /*)
(* NegativeBoundary are c1092mabo_positiveSource / c1092mabo_negativeBoundary*)
(* (the OpenSquare invariants of the witness are added to the existentials). *)
(* MissingBoundaryShallow CentralProfile / ActualFrames / actual_shallow:    *)
(* c1092mbsa_central_profile / c1092mbsa_frames / C1092MBSA_ACTUAL_SHALLOW;  *)
(* PositiveBoundaryOrigin Input / origin: c1092pbot_input / C1092PBOT_ORIGIN;*)
(* MissingPositiveBoundaries Data / of_inputs / profile: c1092mpbp_data /    *)
(* C1092MPBP_DATA_OF_INPUTS / C1092MPBP_PROFILE; MissingPositiveFaces.Faces: *)
(* c1092mmpf_faces; WallProfileScalars half / quarter_data: C1092WPS_half /  *)
(* C1092WPS_QUARTER_DATA; cosine_order C977CSB_COSINE_ORDER.  The triple     *)
(* MMMPEndingAxes.clockwise of B = (c,s,u,v,a) is (c, s, v, --u - a, a).     *)
(* owner_frame is C1092MPOA_OWNER_FRAME.  Tag C1092MABO_.                    *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMActualNegativeHalfpoint.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingBoundaryShallowActual.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveBoundaryOrigin.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveForwardUpperCap.ml";;
needs "n12/geometry/CP_C1092_MPPMPositiveOriginWallAngle.ml";;
needs "n12/geometry/CP_C1092_MPPMMissingPositiveBoundProfiles.ml";;
needs "n12/geometry/CP_C1092_MMMP_EndingAxes.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;

(* Lean: side_gt (private) *)
let C1092MABO_SIDE_GT = C1092MPAPO_SIDE_GT;;
(* Lean: mark (private) *)
let C1092MABO_MARK = C1092MPAPO_MARK;;

let C1092MABO_V = C1092MPPE_V;;
let C1092MABO_CV = [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`];;
let C1092MABO_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;
let c1092mabo_normal_tac c s =
  let n = list_mk_comb(`c977cc_normal`, [c; s]) in
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o check (fun th -> concl th = n)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o check (fun th -> concl th = n));;
(* prove the point goal ~linside/linside C x y by contradiction from linear facts *)
let c1092mabo_point_tac tm =
  UNDISCH_TAC tm THEN REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN C1092MABO_LP_TAC;;

(* Lean: halfpoint_floor *)
let C1092MABO_HALFPOINT_FLOOR = prove
 (`forall cC sC uC vC aC.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ &1 < aC /\ c977cc_normal cC sC /\ &0 < sC /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\
     linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
     ~linside cC sC uC vC aC (--(&1)) (--(&1 / &2)) /\
     ~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20)
     ==> --cC - sC / &2 <= uC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mabo_normal_tac `cC:real` `sC:real` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `sC - cC / &2 <= vC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    c1092mabo_point_tac `~linside cC sC uC vC aC (--(&1)) (--(&1 / &2))`; ALL_TAC] THEN
  SUBGOAL_THEN `&13 * sC < &3 * cC` ASSUME_TAC THENL
   [UNDISCH_TAC `linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20))` THEN
    REWRITE_TAC[linside] THEN UNDISCH_TAC `sC - cC / &2 <= vC` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `vC + aC <= (&7 / &20) * (cC + sC)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    c1092mabo_point_tac `~linside cC sC uC vC aC (--(&7 / &20)) (&7 / &20)`; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: owner_frame *)
let C1092MABO_OWNER_FRAME = C1092MPOA_OWNER_FRAME;;

(* Lean: PositiveSource (structure) *)
let c1092mabo_positiveSource = new_definition (parse_term (Printf.sprintf
  "c1092mabo_positiveSource (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                            (cC:real) (sC:real) (uC:real) (vC:real) (aC:real) <=>
     c1092psa_frame c1 c2 a b l cC sC uC vC aC /\\ c977cc_normal cC sC /\\ &0 < sC /\\
     %s /\\ ~%s /\\ --cC - sC / &2 <= uC /\\ vC + aC <= sC"
  (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&1" "&2")));;

(* Lean: corner_segment *)
let C1092MABO_CORNER_SEGMENT = prove
 (parse_term (Printf.sprintf "!%s y. %s /\\ --(&543 / &500) <= y /\\ y <= --(&1) ==> %s"
    C1092AE_P C1092AE_HYP (c1092mppe_in 0 "&1" "&2 + y")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC C1092PSA_CODE_CONV THEN
  MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&457 / &500`; `&1`] THEN
  REWRITE_TAC[c1092psa_seed 0 (`&1`, `&457 / &500`); c1092psa_seed 0 (`&1`, `&1`)] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: missing_crosspoint_caps *)
let C1092MABO_MISSING_CROSSPOINT_CAPS = prove
 (`forall cC sC uC vC aC.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ &1 < aC /\ c977cc_normal cC sC /\
     c1092mmpf_faces cC sC uC vC aC /\
     linside cC sC uC vC aC (--(&1)) (--(&2 / &5)) /\ ~linside cC sC uC vC aC (--(&1 / &2)) (&0)
     ==> uC + aC <= --cC / &2 /\ &1 + cC < &3 * sC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN c1092mabo_normal_tac `cC:real` `sC:real` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mmpf_faces] o check (c1092mpapo_head `c1092mmpf_faces`)) THEN
  SUBGOAL_THEN `uC + aC <= --cC / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    c1092mabo_point_tac `~linside cC sC uC vC aC (--(&1 / &2)) (&0)`; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 < cC / &2 + sC` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half cC sC < &1` ASSUME_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&7 / &10 <= c ==> &0 < &1 + c`;
      ASSUME `&7 / &10 <= cC`] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &3 < C1092WPS_half cC sC` ASSUME_TAC THENL
   [MAP_EVERY (fun t -> UNDISCH_TAC t)
      [`(&1 + C1092WPS_half cC sC pow 2) * cC = &1 - C1092WPS_half cC sC pow 2`;
       `(&1 + C1092WPS_half cC sC pow 2) * sC = &2 * C1092WPS_half cC sC`;
       `C1092WPS_half cC sC < &1`; `&1 < cC / &2 + sC`] THEN
    SPEC_TAC(`C1092WPS_half cC sC`, `q:real`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(&1 + q pow 2) * (cC / &2 + sC - &1) = (&1 - q) * (&3 * q - &1) / &2` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&1 + q pow 2) * (cC / &2 + sC - &1)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
       [MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(&1 - q) * (&3 * q - &1) <= &0` MP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&0 <= x * --y ==> x * y <= &0`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (C1092WPS_half cC sC - &1 / &3) * (&1 + cC)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* Lean: steep_sine *)
let C1092MABO_STEEP_SINE = prove
 (`forall c s. c977cc_normal c s /\ &1 + c < &3 * s ==> &3 / &5 < s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&4 / &5`; `&3 / &5`; `c:real`; `s:real`] C977CSB_COSINE_ORDER) THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

let C1092MABO_CT = C1092MPOA_CT;;
(* (owners p i).translated 2 2, literal mask *)
let c1092mabo_tr i =
  let [c; s; u; v; _] = c1092psa_own i in
  let t = SPECL [c; s; u; v; `l:real`; `&2`; `&2`; `x:real`; `y:real`] C1092PSA_INSIDE_TRANSLATED in
  fst (chop_list 5 (snd (strip_comb (lhs (concl t)))));;
let C1092MABO_SQC = "cC * cC + sC * sC = &1 /\\ &0 < aC";;
let C1092MABO_MISSING9 = "~" ^ c1092mppe_in 9 "&2" "&1";;

(* Lean: positive_source *)
let C1092MABO_POSITIVE_SOURCE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> ?cC sC uC vC aC. %s /\\ c1092mabo_positiveSource %s cC sC uC vC aC"
    C1092AE_P C1092MPAPO_HYPS C1092MABO_MISSING9 C1092MABO_SQC C1092AE_P),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  SUBGOAL_THEN (parse_term (c1092mppe_in 4 "&87 / &50" "&2")) ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC (parse_term C1092MABO_MISSING9) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC (SPECL C1092MABO_V C1092PSA_BOTTOM_ORIGIN_OF_MISSING) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL C1092MABO_V C1092PSA_EXISTS_CANONICAL_FRAME) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `cC:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sC:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `uC:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `vC:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `aC:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c1092mabo_positiveSource] THEN
  MP_TAC(SPECL C1092MABO_CV (SPECL C1092MABO_V C1092MABO_OWNER_FRAME)) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < sC` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC (parse_term C1092MABO_MISSING9) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC (SPECL (C1092MABO_V @ C1092MABO_CT) C1092MANH_BOTTOM_ORIGIN) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `c977cc_normal cC sC` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mppe_in 4 "&1" "&2"))) ASSUME_TAC THENL
   [MATCH_MP_TAC (SPECL (C1092MABO_V @ C1092MABO_CT) C1092MANH_SOUTHWEST_POSITIVE_PREVIOUS_EXCLUDED) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
    MP_TAC(SPECL C1092MABO_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MABO_V @ C1092MABO_CV) C1092PSA_FORWARD_CORE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL C1092MABO_CV C1092PCS_FORWARD_PROFILE) THEN
  ASM_REWRITE_TAC[c1092pcs_forwardFaces] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL C1092MABO_V C1092FPDA_CORNER_HALFPOINT_OF_MISSING_BOTTOM_ORIGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092pcs_forwardCore] o check (c1092mpapo_head `c1092pcs_forwardCore`)) THEN
  MATCH_MP_TAC C1092MABO_HALFPOINT_FLOOR THEN MAP_EVERY EXISTS_TAC [`vC:real`; `aC:real`] THEN ASM_REWRITE_TAC[] THEN
  C1092MPAPO_FRAME_TAC THEN CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  CONJ_TAC THENL
   [ACCEPT_TAC(c1092psa_excl 4 0 (c1092mano_lasm 0 "&1" "&3 / &2"));
    ACCEPT_TAC(c1092psa_excl 4 7 (c1092psa_seed 7 (`&33 / &20`, `&47 / &20`)))]);;

(* Lean: PositiveSource.complete *)
let C1092MABO_POSITIVESOURCE_COMPLETE = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ %s /\\ c1092mabo_positiveSource %s cC sC uC vC aC
      ==> c1092mbsa_central_profile cC sC uC vC aC" C1092AE_P C1092MPAPO_HYPS C1092MABO_SQC C1092AE_P),
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mabo_positiveSource; c1092mbsa_central_profile] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC (SPECL (C1092MABO_V @ C1092MABO_CV) C1092MPFUC_UPPER_CAP) THEN ASM_REWRITE_TAC[]);;

(* Lean: NegativeBoundary (structure) *)
let c1092mabo_negativeBoundary = new_definition (parse_term (Printf.sprintf
  "c1092mabo_negativeBoundary (c1:num->real) (c2:num->real) (a:num->real) (b:num->real) (l:real)
                              (cB:real) (sB:real) (uB:real) (vB:real) (aB:real) <=>
     aB = l /\\ (!x y. linside cB sB uB vB aB x y <=> %s) /\\
     c977cc_normal cB (--sB) /\\ &0 < --sB /\\ --sB / cB < &1 / &4"
  (c1092mppe_in 9 "&2 + x" "&2 + y")));;

let C1092MABO_BV = [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`];;

(* Lean: missing_bottom_negative *)
let C1092MABO_MISSING_BOTTOM_NEGATIVE = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s ==> ?cB sB uB vB aB. cB * cB + sB * sB = &1 /\\ &0 < aB /\\
      c1092mabo_negativeBoundary %s cB sB uB vB aB"
    C1092AE_P C1092MPAPO_HYPS C1092MABO_MISSING9 C1092AE_P),
  (REPEAT GEN_TAC THEN STRIP_TAC) THEN
  (MP_TAC(SPECL C1092MABO_V C1092MABO_POSITIVE_SOURCE) THEN ASM_REWRITE_TAC[]) THEN
  (MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) C1092MABO_CV THEN STRIP_TAC) THEN
  (MP_TAC(SPECL (C1092MABO_V @ C1092MABO_CV) C1092MABO_POSITIVESOURCE_COMPLETE)) THEN
  (ASM_REWRITE_TAC[] THEN DISCH_TAC) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mabo_positiveSource] o
    check (c1092mpapo_head `c1092mabo_positiveSource`))) THEN
  (C1092MPAPO_ORD_TAC) THEN
  (MP_TAC(SPECL (c1092mabo_tr 9) CLF_CANONICAL_FRAME)) THEN
  (ANTS_TAC THENL [REWRITE_TAC[c1092psa_unit 9; c1092psa_pos ()]; ALL_TAC]) THEN
  (MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `cB:real`) THEN
  (MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `sB:real`) THEN
  (MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `uB:real`) THEN
  (MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `vB:real`) THEN
  (MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `aB:real` THEN STRIP_TAC) THEN
  (FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = l` || concl th = `aB:real = l`))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[C1092PSA_INSIDE_TRANSLATED]) THEN
  MP_TAC(SPECL C1092MABO_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAWR_BOTTOM_ORDINARY THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mbsa_central_profile] o check (c1092mpapo_head `c1092mbsa_central_profile`)) THEN
  SUBGOAL_THEN (parse_term "c1092mbsa_frames c1 c2 a b l cC sC uC vC l cB sB uB vB l") ASSUME_TAC THENL
   [REWRITE_TAC[c1092mbsa_frames] THEN CONV_TAC C1092PSA_CODE_CONV THEN
    RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC]) THEN
  (REWRITE_TAC[c1092mabo_negativeBoundary] THEN CONV_TAC C1092PSA_CODE_CONV THEN
  RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN ASM_REWRITE_TAC[]) THEN
  (SUBGOAL_THEN `&0 < --sB` ASSUME_TAC) THENL
   [(REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg (concl th) && can (find_term ((=) `8192`)) (concl th) &&
     can (find_term ((=) `&2`)) (concl th) && not (is_forall (dest_neg (concl th))))) THEN
  MP_TAC(SPECL ([`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`; `cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`]) C1092PBOT_ORIGIN) THEN
  ASM_REWRITE_TAC[c1092pbot_input; ldisj] THEN CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  MATCH_MP_TAC(TAUT `p ==> (p ==> q) ==> q`)) THEN
    (let wa = c1092psa_wa () in
  REWRITE_TAC[c1092psa_seed 9 (`&2`, `&457 / &500`); CONJUNCT1 (CONJUNCT2 wa); c1092psa_apart 4 9] THEN
  ASM_REWRITE_TAC[]) THEN
    (REPEAT CONJ_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[lcont] (c1092psa_box 9))) THEN
    REAL_ARITH_TAC;
    REPEAT STRIP_TAC THEN
    MP_TAC(SPECL (C1092MABO_V @ [`y:real`]) C1092MABO_CORNER_SEGMENT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONV_TAC C1092PSA_CODE_CONV THEN
    MP_TAC(SPECL [`&1`; `&2 + y`] (c1092psa_apart 9 0)) THEN ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  (SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
   [REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL (C1092MABO_V @ [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `l:real`] @
                [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `l:real`]) C1092MBSA_ACTUAL_SHALLOW) THEN
  CONV_TAC C1092PSA_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092PSA_CODE_CONV) THEN
  ASM_REWRITE_TAC[c1092mbsa_central_profile] THEN SIMP_TAC[]));;

let C1092MABO_SIDE_TAC =
  SUBGOAL_THEN `&1 < aC` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[c1092psa_frame] o check (c1092mpapo_head `c1092psa_frame`)) THEN
    MP_TAC(SPECL C1092MABO_V OO_SIDE) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC];;

(* the triple clockwise turn of MMMPEndingAxes *)
let C1092MABO_INSIDE_CLOCKWISE3 = prove
 (`forall c s u v a x y. linside c s v (--u - a) a x y <=> linside c s u v a (--y) x`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1092MABO_PHYPS = Printf.sprintf "%s /\\ %s /\\ c977cc_normal cC sC /\\ &0 < sC" C1092MPAPO_HYPS C1092MPOA_CHYPS;;

(* Lean: missing_positive_previous_excluded *)
let C1092MABO_MISSING_POSITIVE_PREVIOUS_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s ==> ~%s"
    C1092AE_P C1092MABO_PHYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092mppe_in 8 "&1" "&2"))) ASSUME_TAC THENL
   [c1092mano_excl_tac 8 4 `&1` `&2`; ALL_TAC] THEN
  c1092manh_rot_ord_tac 3 THEN
  SUBGOAL_THEN (mk_neg (parse_term (c1092ae_in "d1 d2 e1 e2 l" 9 "&2" "&1"))) ASSUME_TAC THENL
   [c1092mpapo_pull_tac (c1092mpapo_d4 "") `(true,false,true)` [9] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL C1092MANH_D5 C1092MABO_MISSING_BOTTOM_NEGATIVE) THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun v -> DISCH_THEN(X_CHOOSE_THEN v MP_TAC)) C1092MABO_BV THEN
  REWRITE_TAC[c1092mabo_negativeBoundary] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aB:real = l`)) THEN
  SUBGOAL_THEN `c1092powa_leftFrame c1 c2 a b l cB sB vB (--uB - l) l` ASSUME_TAC THENL
   [REWRITE_TAC[c1092powa_leftFrame; C1092MABO_INSIDE_CLOCKWISE3] THEN ASM_REWRITE_TAC[] THEN
    c1092mpapo_pull_tac (c1092mpapo_d4 "") `(true,false,true)` [9] THEN
    REWRITE_TAC[REAL_ARITH `&4 - (&2 + --y) = &2 + y`];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MABO_V @ C1092MABO_CV @ [`cB:real`; `sB:real`; `vB:real`; `--uB - l`; `l:real`])
    C1092POWA_ACTUAL_STEEP) THEN
  ASM_REWRITE_TAC[] THEN
  c1092mabo_normal_tac `cB:real` `--sB` THEN
  UNDISCH_TAC `--sB / cB < &1 / &4` THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&7 / &10 <= c ==> &0 < c`] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: positive_previous_excluded *)
let C1092MABO_POSITIVE_PREVIOUS_EXCLUDED = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> ~%s"
    C1092AE_P C1092MABO_PHYPS (c1092mppe_in 4 "&1" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 4 "&87 / &50" "&2")) THENL
   [MATCH_MP_TAC (SPECL (C1092MABO_V @ C1092MABO_CV) C1092MPOA_PREVIOUS_ABSENT);
    MATCH_MP_TAC (SPECL (C1092MABO_V @ C1092MABO_CV) C1092MABO_MISSING_POSITIVE_PREVIOUS_EXCLUDED)] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: missing_positive_data *)
let C1092MABO_MISSING_POSITIVE_DATA = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s ==> c1092mpbp_data cC sC uC vC aC"
    C1092AE_P C1092MABO_PHYPS (c1092mppe_in 4 "&87 / &50" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL (C1092MABO_V @ C1092MABO_CV) C1092MABO_POSITIVE_PREVIOUS_EXCLUDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  MATCH_MP_TAC C1092MPBP_DATA_OF_INPUTS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC (SPECL (C1092MABO_V @ C1092MABO_CV) C1092PSA_MISSING_INPUTS) THEN ASM_REWRITE_TAC[];
    C1092MPAPO_FRAME_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: positive_faces *)
let C1092MABO_POSITIVE_FACES = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s ==> c1092pcs_forwardFaces cC sC uC vC aC /\\ uC + aC <= &0"
    C1092AE_P C1092MABO_PHYPS),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (parse_term (c1092mppe_in 4 "&87 / &50" "&2")) THENL
   [MATCH_MP_TAC (SPECL (C1092MABO_V @ C1092MABO_CV) C1092MPFUC_FACES) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL (C1092MABO_V @ C1092MABO_CV) C1092MABO_MISSING_POSITIVE_DATA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MABO_SIDE_TAC THEN
  MP_TAC(SPECL C1092MABO_CV C1092MPBP_PROFILE) THEN ASM_REWRITE_TAC[c1092mpbp_profile] THEN STRIP_TAC THEN
  c1092mabo_normal_tac `cC:real` `sC:real` THEN
  REWRITE_TAC[c1092pcs_forwardFaces] THEN ASM_REAL_ARITH_TAC);;

(* Lean: actual_missing_crosspoint_caps *)
let C1092MABO_ACTUAL_MISSING_CROSSPOINT_CAPS = prove
 (parse_term (Printf.sprintf "!%s cC sC uC vC aC. %s /\\ ~%s /\\ ~%s ==> uC + aC <= --cC / &2 /\\ &1 + cC < &3 * sC"
    C1092AE_P C1092MABO_PHYPS (c1092mppe_in 4 "&87 / &50" "&2") (c1092mppe_in 4 "&3 / &2" "&2")),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  c1092mpapo_use C1092MPAPO_FAR_POINTS THEN STRIP_TAC THEN C1092MPAPO_ORD_TAC THEN
  MP_TAC(SPECL (C1092MABO_V @ C1092MABO_CV) C1092PSA_MISSING_PROFILE) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C1092MABO_SIDE_TAC THEN
  MATCH_MP_TAC C1092MABO_MISSING_CROSSPOINT_CAPS THEN EXISTS_TAC `vC:real` THEN
  ASM_REWRITE_TAC[] THEN C1092MPAPO_FRAME_TAC THEN ASM_REWRITE_TAC[]);;

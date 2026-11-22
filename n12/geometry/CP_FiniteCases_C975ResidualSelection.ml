(* ========================================================================= *)
(* Phase 2: Compact/Completion/FiniteCases/C975ResidualSelection.lean        *)
(* (namespace N12Compact.FiniteCases.C975Selection; Lean header: "Source     *)
(* translation only").  Further C975 cuts after the merged-top origin.       *)
(* owner p m is the 5-tuple (ooc .. m) .. l; auxiliaries p m is ooaux .. m.  *)
(* The frame r of southeast_outward_frame is cr sr ur vr ar with its unit    *)
(* normal and positive side explicit; (pullY q).Inside x y is stated as      *)
(* q.Inside x (4 - y) (LINSIDE_PULLY); Faces = ocobp_faces.  S12             *)
(* inside_segment on the vertical right segment: OO_VERTICAL_SEGMENT.        *)
(* OutwardBarFrame.frame_original: OCOBF_FRAME_ORIGINAL; UpperBarPoint.      *)
(* point_original: OCUBP_POINT_ORIGINAL; SharpPointScalars.half_upper /      *)
(* half_lower: OCSPS_HALF_UPPER / OCSPS_HALF_LOWER; OutwardPair.impossible:  *)
(* OCOP_IMPOSSIBLE; CrossedElbow.point_original: OCCE_POINT_ORIGINAL.        *)
(* Tag C975RS_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/CP_FiniteCases_C975TopOrigin.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarFrame.ml";;
needs "n12/geometry/CP_OtherCases_OutwardPair.ml";;
needs "n12/geometry/CP_OtherCases_UpperBarPoint.ml";;

(* Lean: right_bar *)
let C975RS_RIGHT_BAR = prove
 (`forall c1 c2 a b l y. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c975d_family /\
     &113 / &50 <= y /\ y <= &64 / &25
     ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384) (oov c1 c2 a b l 16384) l (&3) y`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&113 / &50`; `&64 / &25`] THEN
  ASM_SIMP_TAC[C975SS_RIGHT_F9; C975IC_RIGHT_HIGH] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let C975RS_CONV = REWRITE_CONV[LINSIDE_PULLX; LINSIDE_PULLY; LINSIDE_PULLSW] THENC REAL_RAT_REDUCE_CONV;;
let C975RS_FRAME_LEMMA = CONV_RULE C975RS_CONV (SPECL (c975ss_pully (c975ic_owner 512)) OCOBF_FRAME_ORIGINAL);;

(* Lean: southeast_outward_frame *)
let C975RS_SOUTHEAST_OUTWARD_FRAME = prove
 (c975ic_stmt [mk_neg (c975ic_own 512 `&113 / &50` `&2`)]
   (rand (concl C975RS_FRAME_LEMMA)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975SF_APPLY_TAC OCOBF_FRAME_ORIGINAL (c975ss_pully (c975ic_owner 512))
   [C975SS_SE_MARKER; C975SS_SE_F8; C975SS_SOUTHEAST_G8_POINT]
   [16384, C975SS_RIGHT_MARKER; 12, C975SS_SE_CORNER; 12, C975SS_SE_CORNER_RIGHT;
    8192, C975SEL_BOTTOM_BAR]);;

let C975RS_CORNER = c975ss_seed_point 48 (`&3`, `&3`);;

(* Lean: northeast_upper_sharp *)
let C975RS_NORTHEAST_UPPER_SHARP = prove
 (c975ic_stmt [mk_neg (c975ic_own 1024 `&2` `&113 / &50`)] (c975ic_own 1024 `&101 / &40` `&17 / &8`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C975SF_APPLY_TAC OCUBP_POINT_ORIGINAL (c975ic_owner 1024)
   [C975SS_NE_MARKER; C975SF_NORTHEAST_F7_POINT]
   [34816, C975TO_TOP_ORIGIN; 48, C975RS_CORNER; 16384, C975RS_RIGHT_BAR]);;

let c975rs_lin q x y = list_mk_comb(`linside`, q @ [x; y]);;
let c975rs_tr22 [c; s; u; v; a] =
  [c; s; mk_binop `(-):real->real->real` u
           (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` c `&2`)
                                            (mk_binop `( * ):real->real->real` s `&2`));
   mk_binop `(-):real->real->real` v
           (mk_binop `(+):real->real->real` (mk_binop `( * ):real->real->real` (mk_comb(`(--):real->real`, s)) `&2`)
                                            (mk_binop `( * ):real->real->real` c `&2`)); a];;

let C975RS_A = c975rs_tr22 (c975ss_pully [`cr:real`; `sr:real`; `ur:real`; `vr:real`; `l:real`]);;
let C975RS_N = c975rs_tr22 (c975ic_owner 1024);;
let C975RS_A_LEMMA = list_mk_forall([`x:real`; `y:real`],
  mk_iff(c975rs_lin C975RS_A `x:real` `y:real`, c975rs_lin (c975ic_owner 512) `&2 + x` `&2 + y`));;
let C975RS_N_LEMMA = list_mk_forall([`x:real`; `y:real`],
  mk_iff(c975rs_lin C975RS_N `x:real` `y:real`, c975rs_lin (c975ic_owner 1024) `&2 + x` `&2 + y`));;

(* Lean: outward_mixed_impossible *)
let C975RS_OUTWARD_MIXED_IMPOSSIBLE = prove
 (c975ic_stmt [mk_neg (c975ic_own 512 `&113 / &50` `&2`); c975ic_own 1024 `&2` `&113 / &50`] `false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL C975SF_SOUTHEAST_OUTWARD_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPEC_ALL C975RS_SOUTHEAST_OUTWARD_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cr:real` (X_CHOOSE_THEN `sr:real` (X_CHOOSE_THEN `ur:real`
    (X_CHOOSE_THEN `vr:real` (X_CHOOSE_THEN `ar:real` (STRIP_ASSUME_TAC o REWRITE_RULE[ocobp_faces])))))) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `(ar:real) = l`)) THEN
  SUBGOAL_THEN C975RS_A_LEMMA ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&2 + x`; `&2 - y`] o check (fun th ->
      is_forall(concl th) && is_iff(snd(strip_forall(concl th))))) THEN
    REWRITE_TAC[REAL_ARITH `&4 - (&2 - y) = &2 + y`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN C975RS_N_LEMMA ASSUME_TAC THENL
   [REWRITE_TAC[linside] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `cr pow 2 + sr pow 2 = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_POW_2]; ALL_TAC] THEN
  MP_TAC (SPECL [`cr:real`; `sr:real`; `&143 / &500`] OCSPS_HALF_UPPER) THEN
  MP_TAC (SPECL [`cr:real`; `sr:real`; `&37 / &50`] OCSPS_HALF_LOWER) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  MP_TAC (SPECL (C975RS_A @ C975RS_N @ [`sr:real`]) OCOP_IMPOSSIBLE) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[ldisj] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN NO_TAC;
         ASM_SIMP_TAC[OO_UNIT] THEN NO_TAC;
         MP_TAC (SPEC_ALL OO_SIDE) THEN ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
         ASM_SIMP_TAC[C975SS_SE_MARKER; C975SS_NE_MARKER; C975SEL_NORTHEAST_SELECTION] THEN NO_TAC;
         C975IC_FOREIGN_TAC 34816 C975SS_NW_MARKER;
         C975IC_FOREIGN_TAC 34816 C975TO_TOP_ORIGIN;
         C975IC_FOREIGN_TAC 48 C975RS_CORNER;
         MP_TAC (SPEC_ALL (oo_apart C975D_F 512 1024)) THEN ASM_REWRITE_TAC[ldisj] THEN
         DISCH_TAC THEN ASM_REWRITE_TAC[]]);;

(* Lean: southeast_g6_point *)
let C975RS_SOUTHEAST_G6_POINT = prove
 (c975ic_stmt [] (c975ic_own 512 `&113 / &50` `&2`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC (c975ic_own 512 `&113 / &50` `&2`) THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC (c975ic_own 1024 `&2` `&113 / &50`) THENL
   [MATCH_MP_TAC C975RS_OUTWARD_MIXED_IMPOSSIBLE THEN MAP_EVERY EXISTS_TAC C975IC_V5 THEN
    ASM_REWRITE_TAC[];
    MP_TAC (SPEC_ALL C975SF_SOUTHEAST_OUTWARD_SHARP) THEN
    MP_TAC (SPEC_ALL C975RS_NORTHEAST_UPPER_SHARP) THEN ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    MP_TAC (SPEC_ALL (oo_apart C975D_F 512 1024)) THEN ASM_REWRITE_TAC[ldisj] THEN
    DISCH_THEN (MP_TAC o SPECL [`&101 / &40`; `&17 / &8`]) THEN ASM_REWRITE_TAC[]]);;

(* Lean: southeast_g6 *)
let C975RS_SOUTHEAST_G6 = prove
 (c975ic_stmt [] (c975ic_mem 16 512),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM (oo_aux_point 16)] THEN
  ASM_SIMP_TAC[C975RS_SOUTHEAST_G6_POINT]);;

(* Lean: not_northeast_g6 *)
let C975RS_NOT_NORTHEAST_G6 = prove
 (c975ic_stmt [] (mk_neg (c975ic_mem 16 1024)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM (oo_aux_point 16)] THEN
  C975IC_FOREIGN_TAC 512 C975RS_SOUTHEAST_G6_POINT);;

(* Lean: not_southeast_f5 *)
let C975RS_NOT_SOUTHEAST_F5 = prove
 (c975ic_stmt [] (mk_neg (c975ic_mem 5 512)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM (oo_aux_point 5)] THEN DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg (c975ic_own 1024 `&2` `&113 / &50`)) ASSUME_TAC THENL
   [C975IC_FOREIGN_TAC 512 (ASSUME (c975ic_own 512 `&2` `&113 / &50`)); ALL_TAC] THEN
  SUBGOAL_THEN (c975ic_own 512 `&101 / &40` `&17 / &8`) ASSUME_TAC THENL
   [C975SF_APPLY_TAC OCCE_POINT_ORIGINAL (c975ic_owner 512)
     [C975SS_SE_MARKER; C975RS_SOUTHEAST_G6_POINT; C975SS_SE_F8]
     [256, C975SS_SOUTHWEST_SOUTH];
    ALL_TAC] THEN
  MP_TAC (SPEC_ALL C975RS_NORTHEAST_UPPER_SHARP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (SPEC_ALL (oo_apart C975D_F 512 1024)) THEN ASM_REWRITE_TAC[ldisj] THEN
  DISCH_THEN (MP_TAC o SPECL [`&101 / &40`; `&17 / &8`]) THEN ASM_REWRITE_TAC[]);;

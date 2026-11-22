(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/BottomBoundaryOrder.lean            *)
(* (N12Compact.C1092MMMPBottomBoundaryOrder).  DOUBLE-RIGHT-BOTTOM-ORIGIN    *)
(* section 1.2.  half: C1092WPS_half; Normal: c977cc_normal;                 *)
(* PositiveInwardHalfangle: C1092MPIH_ENTRANCE / C1092MPIH_POINT;            *)
(* WallProfile.positive_frame: OCWPSG_POSITIVE_FRAME;                        *)
(* square_support_bound (for the wall x <= 2) is replaced by the corner      *)
(* lemma C1092BBO_CORNER.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MMMP_PositiveInwardHalfangle.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;
needs "n12/geometry/SectionCapacity.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

let C1092BBO_LIN_TAC = NLIN_TAC ~deg2:false [];;

let C1092BBO_LE_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBO_LIN_TAC; DISCH_TAC];;

let C1092BBO_LT_MUL_TAC x y =
  MP_TAC(SPECL [x; y] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBO_LIN_TAC; DISCH_TAC];;

(* Lean: Data (structure) *)
let c1092bbo_data = new_definition
 `c1092bbo_data (cC:real) (sC:real) (uC:real) (vC:real) (aC:real)
                (cR:real) (sR:real) (uR:real) (vR:real) (aR:real) <=>
    &0 < cR /\ &0 < sR /\
    cR + sR * C1092WPS_half cC sC <= uR /\
    uR < (&543 / &500) * cR /\
    vR < --(&543 / &500) * sR /\
    cR * (uR + aR) - sR * vR <= &2 /\
    &0 < sR * cC - cR * sC`;;

(* the right-most corner of a square bounded by the wall x <= 2 *)
let C1092BBO_CORNER = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\
               (forall x y. linside c s u v a x y ==> x <= &2)
               ==> c * (u + a) - s * v <= &2`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= &2 - z ==> z <= &2`) THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c + s`] THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c * (u + a - t) - s * (v + t)`;
                                `s * (u + a - t) + c * (v + t)`]) THEN
  ASM_SIMP_TAC[TSS_INSIDE_FACE] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC]);;

(* Lean: angle_order (private) *)
let C1092BBO_ANGLE_ORDER = prove
 (`forall c s b t u v a.
     c * c + s * s = &1 /\ b * b + t * t = &1 /\
     c977cc_normal c s /\ &2331 / &2669 < c /\ &0 < s /\
     &0 < b /\ &0 < t /\ &1 < a /\
     b + t * C1092WPS_half c s <= u /\
     v < --(&543 / &500) * t /\
     b * (u + a) - t * v <= &2
     ==> &0 < t * c - b * s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term ((=) `C1092WPS_half`)) (concl th))) THEN
  REWRITE_TAC[C1092WPS_half] THEN
  SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [C1092BBO_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(s / (&1 + c)) * (&1 + c) = s /\ &0 < s / (&1 + c)` MP_TAC THENL
   [ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LT_DIV]; ALL_TAC] THEN
  SPEC_TAC(`s / (&1 + c)`,`z:real`) THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN
  (* wallGap *)
  MP_TAC(SPECL [`b:real`; `b + t * z`; `u:real`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBO_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`t:real`; `v:real`; `--(&543 / &500) * t`] REAL_LT_LMUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBO_LIN_TAC; DISCH_TAC] THEN
  C1092BBO_LT_MUL_TAC `b:real` `a - &1` THEN
  SUBGOAL_THEN `b * t * z < &1 - b - (&43 / &500) * t * t` ASSUME_TAC THENL
   [C1092BBO_LIN_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  (* cosineOrder *)
  C1092BBO_LT_MUL_TAC `b:real` `s:real` THEN C1092BBO_LT_MUL_TAC `t:real` `c:real` THEN
  C1092BBO_LE_MUL_TAC `b * s - t * c` `b * s + t * c` THEN
  SUBGOAL_THEN `(b * s - t * c) * (b * s + t * c) = b * b - c * c` ASSUME_TAC THENL
   [UNDISCH_TAC `c * c + s * s = &1` THEN UNDISCH_TAC `b * b + t * t = &1` THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `c <= b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092BBO_LT_MUL_TAC `c - b` `c + b` THEN C1092BBO_LIN_TAC; ALL_TAC] THEN
  (* sineOrder *)
  C1092BBO_LE_MUL_TAC `b - c` `b + c` THEN
  SUBGOAL_THEN `t <= s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092BBO_LT_MUL_TAC `t - s` `t + s` THEN C1092BBO_LIN_TAC; ALL_TAC] THEN
  (* halfOrder *)
  C1092BBO_LE_MUL_TAC `z:real` `b - c` THEN
  SUBGOAL_THEN `t <= z * (&1 + b)` ASSUME_TAC THENL [C1092BBO_LIN_TAC; ALL_TAC] THEN
  C1092BBO_LT_MUL_TAC `b:real` `t:real` THEN
  MP_TAC(SPECL [`b * t`; `t:real`; `z * (&1 + b)`] REAL_LE_LMUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBO_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`b * t * z`; `&1 - b - (&43 / &500) * t * t`; `&1 + b`] REAL_LT_RMUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN C1092BBO_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&0 <= t * t` ASSUME_TAC THENL [REWRITE_TAC[REAL_LE_SQUARE]; ALL_TAC] THEN
  C1092BBO_LE_MUL_TAC `t * t` `(&543 / &500) * b - &457 / &500` THEN
  SUBGOAL_THEN `(&1 - b - (&43 / &500) * t * t) * (&1 + b) - b * t * t =
                t * t * (&457 / &500 - (&543 / &500) * b)` ASSUME_TAC THENL
   [UNDISCH_TAC `b * b + t * t = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  C1092BBO_LIN_TAC);;

(* Lean: exists_frame *)
let C1092BBO_EXISTS_FRAME = prove
 (`forall cC sC uC vC aC cW sW uW vW aW.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     &1 < aC /\ aC = aW /\ c977cc_normal cC sC /\
     linside cC sC uC vC aC (&7 / &20) (&7 / &20) /\
     linside cC sC uC vC aC (&0) (&13 / &50) /\
     linside cC sC uC vC aC (&13 / &50) (&0) /\
     ~linside cC sC uC vC aC (&0) (&0) /\
     ~linside cC sC uC vC aC (&2 / &5) (&1) /\
     ~linside cC sC uC vC aC (&1 / &2) (&1) /\
     linside cW sW uW vW aW (&543 / &500) (&0) /\
     linside cW sW uW vW aW (&1) (&13 / &50) /\
     linside cW sW uW vW aW (&1) (&2 / &5) /\
     ~linside cW sW uW vW aW (&1) (&0) /\
     (forall x y. linside cW sW uW vW aW x y ==> x <= &2) /\
     ldisj cC sC uC vC aC cW sW uW vW aW
     ==> exists cR sR uR vR aR. cR * cR + sR * sR = &1 /\ &0 < aR /\ aR = aW /\
           (forall x y. linside cR sR uR vR aR x y <=> linside cW sW uW vW aW x y) /\
           c1092bbo_data cC sC uC vC aC cR sR uR vR aR`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aW`)) THEN
  SUBGOAL_THEN `~linside cC sC uC vC aC (&1) (&13 / &50)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPIH_ENTRANCE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092MPIH_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aC:real`] OCWPSG_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real`; `t:real`; `p:real`; `q:real`; `a:real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `a:real = aC`)) THEN
  MAP_EVERY EXISTS_TAC [`b:real`; `t:real`; `p:real`; `q:real`; `aC:real`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `linside b t p q aC (&543 / &500) (&0) /\ linside b t p q aC (&1) (&13 / &50) /\
    linside b t p q aC (&1) (&2 / &5) /\ ~linside b t p q aC (&1) (&0) /\
    (forall x y. linside b t p q aC x y ==> x <= &2) /\
    ~linside b t p q aC (&1) (C1092WPS_half cC sC)`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ldisj]; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    can (find_term ((=) `cW:real`)) (concl th)))) THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`b:real`; `t:real`; `p:real`; `q:real`; `aC:real`] C1092BBO_CORNER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `z = C1092WPS_half cC sC` THEN
  REWRITE_TAC[c1092bbo_data] THEN
  (* the frame sine is strictly positive *)
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `b = &1` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `(b - &1) * (b + &1) = &0` MP_TAC THENL
       [UNDISCH_TAC `b * b + &0 * &0 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[REAL_ENTIRE] THEN UNDISCH_TAC `&0 < b` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~linside (&1) (&0) p q aC (&1) (&0)` THEN
    UNDISCH_TAC `linside (&1) (&0) p q aC (&543 / &500) (&0)` THEN
    UNDISCH_TAC `linside (&1) (&0) p q aC (&1) (&13 / &50)` THEN
    REWRITE_TAC[linside] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `b + t * z <= p` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `~linside b t p q aC (&1) z` THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN REWRITE_TAC[linside] THEN
    C1092BBO_LT_MUL_TAC `t:real` `&2 / &5 - z` THEN
    C1092BBO_LT_MUL_TAC `b:real` `z:real` THEN
    C1092BBO_LT_MUL_TAC `b:real` `&13 / &50 - z` THEN
    REPEAT CONJ_TAC THEN C1092BBO_LIN_TAC;
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN
  SUBGOAL_THEN `p < (&543 / &500) * b /\ q < --(&543 / &500) * t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN C1092BBO_LIN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `C1092WPS_half cC sC = z`)) THEN
  MATCH_MP_TAC C1092BBO_ANGLE_ORDER THEN
  MAP_EVERY EXISTS_TAC [`p:real`; `q:real`; `aC:real`] THEN
  ASM_REWRITE_TAC[]);;

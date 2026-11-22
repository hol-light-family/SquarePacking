(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalCentered.lean             *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  The physical joins of       *)
(* CENTERED-INWARD-OIOI sections 6--8.  Squares C W E R B K are the tuples   *)
(* cC sC uC vC aC, cW .., cE .., cR .., cB .., cK ...                        *)
(* BottomCorner B K: c1092ifc_bottomCorner; CenteredPredecessor:             *)
(* c1092mifp_centeredPredecessor; NegativeSuccessor: c1092ifsu_negsucc;      *)
(* Normal: c977cc_normal; half: C1092WPS_half.                               *)
(* (B.translated (-2) (-2)) is the tuple cB sB (uB + &2 * (cB + sB))         *)
(* (vB + &2 * (cB - sB)) aB (C1092IFC_TRANSLATE).                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalPredecessor.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardFinalSuccessor.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_BoundaryOrigin.ml";;

(* Lean: BottomCorner (structure) *)
let c1092ifc_bottomCorner = new_definition
 `c1092ifc_bottomCorner (cB:real) (sB:real) (uB:real) (vB:real) (aB:real)
                        (cK:real) (sK:real) (uK:real) (vK:real) (aK:real) <=>
    &1 < aB /\ aB = aK /\
    (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
    (forall x y. linside cK sK uK vK aK x y ==> --(&2) <= x /\ --(&2) <= y) /\
    linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
    linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
    linside cK sK uK vK aK (--(&1)) (--(&543 / &500)) /\
    linside cK sK uK vK aK (--(&1)) (--(&1)) /\
    ldisj cK sK uK vK aK cB sB uB vB aB`;;

(* Lean: inside_translated_iff at (-2,-2) *)
let C1092IFC_TRANSLATE = prove
 (`forall c s u v a x y.
     linside c s (u + &2 * (c + s)) (v + &2 * (c - s)) a x y <=>
     linside c s u v a (--(&2) + x) (--(&2) + y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let C1092IFC_LIN_TAC =
  FIRST_ASSUM(fun th ->
    if can (term_match [] `linside c s u v a x y`) (concl th)
    then MP_TAC th THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC else NO_TAC);;

let C1092IFC_WALL_TAC =
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o
    check (fun t -> can (MATCH_MP t) th))) THEN REAL_ARITH_TAC;;

let C1092IFC_MISS_TAC =
  DISCH_TAC THEN
  MP_TAC(SPECL [`--(&1)`; `--(&1 / &2)`] (ASSUME
    `forall x y. ~(linside cC sC uC vC aC x y /\ linside cK sK uK vK aK x y)`)) THEN
  REWRITE_TAC[ASSUME `linside cC sC uC vC aC (--(&1)) (--(&1 / &2))`] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[linside] THEN REAL_ARITH_TAC;;

let C1092IFC_DISJ_TAC =
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`--(&2) + x`; `--(&2) + y`] (ASSUME
    `forall x y. ~(linside cK sK uK vK aK x y /\ linside cB sB uB vB aB x y)`)) THEN
  REWRITE_TAC[];;

(* Lean: bottom_origin *)
let C1092IFC_BOTTOM_ORIGIN = prove
 (`forall cC sC uC vC aC cB sB uB vB aB cK sK uK vK aK.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     c1092ifc_bottomCorner cB sB uB vB aB cK sK uK vK aK /\
     linside cC sC uC vC aC (--(&1)) (--(&1 / &2)) /\
     ldisj cC sC uC vC aC cK sK uK vK aK
     ==> linside cB sB uB vB aB (&0) (--(&1))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092ifc_bottomCorner; ldisj] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB + &2 * (cB + sB)`; `vB + &2 * (cB - sB)`; `aB:real`;
                `cK:real`; `sK:real`; `uK + &2 * (cK + sK)`; `vK + &2 * (cK - sK)`; `aK:real`;
                `&457 / &500`; `&8 / &5`] OCWPBO_BOUNDARY_ORIGIN) THEN
  REWRITE_TAC[ldisj; C1092IFC_TRANSLATE] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST
     [FIRST_ASSUM ACCEPT_TAC;
      CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC;
      C1092IFC_WALL_TAC;
      C1092IFC_LIN_TAC;
      C1092IFC_MISS_TAC;
      C1092IFC_DISJ_TAC];
    DISCH_TAC THEN C1092IFC_LIN_TAC]);;

let C1092IFC_LIN =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then (REAL_ARITH_TAC ORELSE RASM_ARITH_TAC) g
            else NLIN_TAC ~deg2:false [] g));;

let C1092IFC_ENDPOINT1 = prove
 (`c977cc_normal (&95727000 / &103958161) (&40541839 / &103958161) /\
   C1092WPS_half (&95727000 / &103958161) (&40541839 / &103958161) = &2869 / &14131`,
  REWRITE_TAC[c977cc_normal; C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let C1092IFC_ENDPOINT2 = prove
 (`c977cc_normal (&4165 / &4813) (&2412 / &4813) /\
   C1092WPS_half (&4165 / &4813) (&2412 / &4813) = &18 / &67`,
  REWRITE_TAC[c977cc_normal; C1092WPS_half] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

(* Lean: centered_halfpoint *)
let C1092IFC_CENTERED_HALFPOINT = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092mifp_centeredPredecessor cC sC uC vC aC cW sW uW vW aW /\ aC = aE /\
     c1092ifsu_negsucc cE sE uE vE aE /\
     linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
     ~linside cE sE uE vE aE (&1) (--(&36 / &85)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> linside cC sC uC vC aC (--(&1)) (--(&1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MIFP_CENTERED_PREDECESSOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mifp_centeredPredecessor] o
    check (can (term_match [] `c1092mifp_centeredPredecessor a b c d e f g h i j`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
    check (fun th -> concl th = `linside cC sC uC vC aC (&0) (&0)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (can (term_match [] `c1092ifsu_negsucc a b c d e`) o concl)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C1092IFSU_SUCCESSOR_FAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092MIFS_RELATIVE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; DISCH_TAC] THEN
  MP_TAC(REWRITE_RULE[C1092IFC_ENDPOINT1] (SPECL [`&95727000 / &103958161`; `&40541839 / &103958161`; `cE:real`; `--sE`]
    C1092MIFE_HALF_CROSS)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092MIFMG_CENTERED_HALF_MARGINS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; STRIP_TAC] THEN
  C1092PRS_NORMAL_TAC THEN
  SUBGOAL_THEN `uC < --cC - sC / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                  `&1 / &2`; `cC / &11 - --sC / &2`] C1092IFSU_SUCCESSOR_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[] THEN C1092IFC_LIN;
    ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
    check (fun th -> can (term_match [] `linside cC sC uC vC aC x y`) (concl th)))) THEN
  REWRITE_TAC[linside] THEN C1092IFC_LIN);;

(* Lean: centered_impossible *)
let C1092IFC_CENTERED_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cW sW uW vW aW cE sE uE vE aE cR sR uR vR aR
    cB sB uB vB aB cK sK uK vK aK.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cW * cW + sW * sW = &1 /\ &0 < aW /\
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cK * cK + sK * sK = &1 /\ &0 < aK /\
     c1092mifp_centeredPredecessor cC sC uC vC aC cW sW uW vW aW /\ aC = aE /\
     c1092ifsu_negsucc cE sE uE vE aE /\
     linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
     aC - cC - (&13 / &50) * sC <= uC + aC /\
     (forall y. --(&36 / &85) <= y /\ y <= &0 ==> linside cR sR uR vR aR (&1) y) /\
     c1092ifc_bottomCorner cB sB uB vB aB cK sK uK vK aK /\
     ldisj cC sC uC vC aC cE sE uE vE aE /\
     ldisj cE sE uE vE aE cR sR uR vR aR /\
     ldisj cC sC uC vC aC cK sK uK vK aK /\
     ldisj cE sE uE vE aE cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~linside cE sE uE vE aE (&1) (--(&36 / &85))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ldisj cE sE uE vE aE cR sR uR vR aR` THEN
    REWRITE_TAC[ldisj; NOT_FORALL_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1`; `--(&36 / &85)`] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C1092IFC_CENTERED_HALFPOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`]
    C1092IFC_BOTTOM_ORIGIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `~linside cE sE uE vE aE (&0) (--(&1))` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `ldisj cE sE uE vE aE cB sB uB vB aB` THEN
    REWRITE_TAC[ldisj; NOT_FORALL_THM] THEN
    MAP_EVERY EXISTS_TAC [`&0`; `--(&1)`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC_ALL C1092MIFP_CENTERED_PREDECESSOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mifp_centeredPredecessor] o
    check (can (term_match [] `c1092mifp_centeredPredecessor a b c d e f g h i j`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[linside] o
    check (fun th -> concl th = `linside cC sC uC vC aC (&0) (&0)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ifsu_negsucc] o
    check (can (term_match [] `c1092ifsu_negsucc a b c d e`) o concl)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C1092IFSU_SUCCESSOR_FAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C1092IFSU_SUCCESSOR_BOTTOM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; STRIP_TAC] THEN
  MP_TAC(REWRITE_RULE[C1092IFC_ENDPOINT2] (SPECL [`&4165 / &4813`; `&2412 / &4813`; `cE:real`; `--sE`]
    C1092MIFE_HALF_CROSS)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092MIFMG_CENTERED_FINAL_MARGINS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; STRIP_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `--sE`] C1092MIFS_RELATIVE_ORDER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092IFC_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `&13 / &50`; `cC / &11 - --sC / &2`] C1092IFSU_SUCCESSOR_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN C1092IFC_LIN);;

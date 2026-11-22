(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/F4SoutheastSign.lean           *)
(* (namespace N12Compact.Completion.OtherCases.C983.F4SoutheastSign).       *)
(* Data: c983fss_data (F4SoutheastSignSupports); lower / upper: ABT_lower / *)
(* ABT_upper; strict_bounds: ABT_STRICT_BOUNDS; ownU / ownV: ABT_OWNU /     *)
(* ABT_OWNV; separated / parallel_radius / transverse_radius: ABT_*;        *)
(* negative_support: C1092MCSUP_NEGATIVE_SUPPORT; faceSeparation_of_       *)
(* disjoint: CSAT_FACESEPARATION_OF_DISJOINT; canonical_frame:              *)
(* CLF_CANONICAL_FRAME.  The private cone / reverse steps of                *)
(* nonnegative_impossible are the helpers C983FSG_CONE / C983FSG_REVCONE.   *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_F4SoutheastSignSupports.ml";;
needs "n12/geometry/CP_C1092_MixedCornerSupports.ml";;
needs "n12/geometry/ClosedFrames.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977ChainBridge.ml";;
needs "n12/geometry/CongruentSAT.ml";;

let C983FSG_NEG_TAC t =
  UNDISCH_TAC t THEN REWRITE_TAC[linside] THEN REWRITE_TAC[] THEN RASM_ARITH_TAC;;

(* Lean: entrance *)
let C983FSG_ENTRANCE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &1 < a /\
     &0 < c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (&0) /\
     linside c s u v a (&1) (--(&13 / &50)) /\
     ~linside c s u v a (&1) (&0) /\
     ~linside c s u v a (&0) (--(&13 / &50))
     ==> c983fss_data c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY UNDISCH_TAC [`linside c s u v a (&7 / &20) (--(&7 / &20))`;
                         `linside c s u v a (&13 / &50) (&0)`;
                         `linside c s u v a (&1) (--(&13 / &50))`] THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u + a <= c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983FSG_NEG_TAC `~linside c s u v a (&1) (&0)`; ALL_TAC] THEN
  SUBGOAL_THEN `--(&13 / &50) * s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983FSG_NEG_TAC `~linside c s u v a (&0) (--(&13 / &50))`; ALL_TAC] THEN
  SUBGOAL_THEN `&1 < c + (&13 / &50) * s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c <= &1 /\ s <= &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN NLIN_TAC [SQ_NONNEG `s:real`; SQ_NONNEG `c:real`;
      SQ_NONNEG `c - &1`; SQ_NONNEG `s - &1`]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < s` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (c + (&13 / &50) * s - &1) * (c + &1 - (&13 / &50) * s)`
    ASSUME_TAC THENL [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `s < &1 / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s * (s - &1 / &2)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `c < &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 < s * s` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN RASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN NLIN_TAC []; ALL_TAC] THEN
  REWRITE_TAC[c983fss_data] THEN RASM_ARITH_TAC);;

let C983FSG_UNIT_TAC =
  REWRITE_TAC[REAL_POW_2] THEN RASM_ARITH_TAC;;

let C983FSG_STRICT sq (x,y) (nx,ny) =
  MP_TAC(SPECL (sq @ [x; y; nx; ny]) ABT_STRICT_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983FSG_UNIT_TAC; STRIP_TAC];;

let c983fsg_wv = [`cw:real`; `sw:real`; `uw:real`; `vw:real`; `aw:real`];;
let c983fsg_ev = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`];;

(* helper: Lean's local `cone` *)
let C983FSG_CONE = prove
 (`forall cw sw uw vw aw cE sE uE vE aE nx ny.
     cw * cw + sw * sw = &1 /\ &0 < aw /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cw sw uw vw aw (--(&7 / &20)) (--(&7 / &20)) /\
     linside cw sw uw vw aw (--(&7 / &20)) (&7 / &20) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     ABT_upper cw sw uw vw aw nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx /\ ny < nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C983FSG_STRICT c983fsg_wv (`--(&7 / &20)`,`--(&7 / &20)`) (`nx:real`,`ny:real`) THEN
  C983FSG_STRICT c983fsg_wv (`--(&7 / &20)`,`&7 / &20`) (`nx:real`,`ny:real`) THEN
  C983FSG_STRICT c983fsg_ev (`&7 / &20`,`--(&7 / &20)`) (`nx:real`,`ny:real`) THEN
  RASM_ARITH_TAC);;

(* helper: Lean's local `reverse` composed with `cone` *)
let C983FSG_REVCONE = prove
 (`forall cw sw uw vw aw cE sE uE vE aE nx ny.
     cw * cw + sw * sw = &1 /\ &0 < aw /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cw sw uw vw aw (--(&7 / &20)) (--(&7 / &20)) /\
     linside cw sw uw vw aw (--(&7 / &20)) (&7 / &20) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cw sw uw vw aw nx ny
     ==> &0 < --nx /\ --ny < --nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C983FSG_CONE THEN
  MAP_EVERY EXISTS_TAC [`cw:real`; `sw:real`; `uw:real`; `vw:real`; `aw:real`;
                        `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN
  ASM_REWRITE_TAC[C1092MCSUP_NEGATIVE_SUPPORT; REAL_POW_NEG; ARITH] THEN
  ASM_REAL_ARITH_TAC);;

let c983fsg_wv' = [`cw:real`; `sw:real`; `uw:real`; `vw:real`; `aE:real`];;
let C983FSG_USE th = MP_TAC th THEN ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN TRY C983FSG_UNIT_TAC THEN TRY ASM_REAL_ARITH_TAC;
   DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[REAL_NEG_NEG])];;
let c983fsg_cone nx ny = C983FSG_USE(SPECL (c983fsg_wv' @ c983fsg_ev @ [nx; ny]) C983FSG_CONE);;
let c983fsg_revcone nx ny = C983FSG_USE(SPECL (c983fsg_wv' @ c983fsg_ev @ [nx; ny]) C983FSG_REVCONE);;
let c983fsg_strictw pt n = C983FSG_STRICT c983fsg_wv' pt n;;
let c983fsg_negsup = MP_TAC(SPECL (c983fsg_wv' @ [`sw:real`; `--cw`]) C1092MCSUP_NEGATIVE_SUPPORT) THEN
  MP_TAC(SPECL (c983fsg_ev @ [`sw:real`; `--cw`]) C1092MCSUP_NEGATIVE_SUPPORT) THEN
  REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC;;

(* Lean: nonnegative_impossible *)
let C983FSG_NONNEGATIVE_IMPOSSIBLE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aE /\ aW = aE /\ &0 < cE /\ &0 <= sE /\ sE <= cE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     linside cW sW uW vW aW (&0) (--(&13 / &50)) /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
     ~linside cE sE uE vE aE (&1) (&0) /\
     ~linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     ldisj cW sW uW vW aW cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL c983fsg_ev C983FSG_ENTRANCE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c983fss_data] o
    check (fun th -> concl th = `c983fss_data cE sE uE vE aE`)) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC c983fsg_wv THEN STRIP_TAC THEN
  SUBGOAL_THEN `ldisj cw sw uw vw aw cE sE uE vE aE` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cW sW uW vW aW cE sE uE vE aE` THEN REWRITE_TAC[ldisj] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) &&
      can (find_term ((=) `cw:real`)) (concl th)
    then RULE_ASSUM_TAC(REWRITE_RULE[GSYM th]) else NO_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aw:real = aW`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aE`)) THEN
  SUBGOAL_THEN `--sw <= cw /\ sw <= cw` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL (c983fsg_wv' @ c983fsg_ev) CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN STRIP_TAC THENL
   [(* W's longitudinal axis *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o
      REWRITE_RULE[GSYM(MP (SPECL [`cw:real`; `sw:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`]
        ABT_PARALLEL_RADIUS) (ASSUME `cw * cw + sw * sw = &1`))]) THEN
    STRIP_TAC THENL
     [ASM_CASES_TAC `&0 <= sw` THENL
       [C983FSG_USE(SPECL (c983fsg_ev @ [`cw:real`; `sw:real`]) C983FSS_POSITIVE_U) THEN
        c983fsg_strictw (`&0`,`&0`) (`cw:real`,`sw:real`) THEN RASM_ARITH_TAC;
        C983FSG_USE(SPECL (c983fsg_ev @ [`cw:real`; `--sw`]) C983FSS_NEGATIVE_W) THEN
        c983fsg_strictw (`&0`,`--(&13 / &50)`) (`cw:real`,`sw:real`) THEN RASM_ARITH_TAC];
      c983fsg_revcone `cw:real` `sw:real` THEN RASM_ARITH_TAC];
    (* W's transverse axis *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o
      REWRITE_RULE[GSYM(MP (SPECL [`cw:real`; `sw:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`]
        ABT_TRANSVERSE_RADIUS) (ASSUME `cw * cw + sw * sw = &1`))]) THEN
    STRIP_TAC THENL
     [c983fsg_cone `--sw` `cw:real` THEN RASM_ARITH_TAC;
      c983fsg_revcone `--sw` `cw:real` THEN
      C983FSG_USE(SPECL (c983fsg_ev @ [`cw:real`; `sw:real`]) C983FSS_POSITIVE_V) THEN
      c983fsg_negsup THEN
      c983fsg_strictw (`&0`,`--(&13 / &50)`) (`sw:real`,`--cw`) THEN RASM_ARITH_TAC];
    (* E's longitudinal axis *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o
      REWRITE_RULE[GSYM(ONCE_REWRITE_RULE[REAL_ADD_SYM] (MP (SPECL [`cE:real`; `sE:real`; `aE:real`; `cw:real`; `sw:real`; `aE:real`]
        ABT_PARALLEL_RADIUS) (ASSUME `cE * cE + sE * sE = &1`)))]) THEN
    STRIP_TAC THENL
     [C983FSG_USE(SPECL c983fsg_ev ABT_OWNU) THEN
      c983fsg_strictw (`&0`,`&0`) (`cE:real`,`sE:real`) THEN RASM_ARITH_TAC;
      c983fsg_revcone `cE:real` `sE:real` THEN RASM_ARITH_TAC];
    (* E's transverse axis *)
    FIRST_X_ASSUM(MP_TAC o MATCH_MP ABT_SEPARATED o
      REWRITE_RULE[GSYM(ONCE_REWRITE_RULE[REAL_ADD_SYM] (MP (SPECL [`cE:real`; `sE:real`; `aE:real`; `cw:real`; `sw:real`; `aE:real`]
        ABT_TRANSVERSE_RADIUS) (ASSUME `cE * cE + sE * sE = &1`)))]) THEN
    STRIP_TAC THENL
     [c983fsg_cone `--sE` `cE:real` THEN RASM_ARITH_TAC;
      C983FSG_USE(SPECL c983fsg_ev ABT_OWNV) THEN
      MP_TAC(SPECL (c983fsg_wv' @ [`sE:real`; `--cE`]) C1092MCSUP_NEGATIVE_SUPPORT) THEN
      MP_TAC(SPECL (c983fsg_ev @ [`sE:real`; `--cE`]) C1092MCSUP_NEGATIVE_SUPPORT) THEN
      REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC THEN
      c983fsg_strictw (`&0`,`--(&13 / &50)`) (`sE:real`,`--cE`) THEN RASM_ARITH_TAC]]);;

(* Lean: canonical_negative *)
let C983FSG_CANONICAL_NEGATIVE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aE /\ aW = aE /\ &0 < cE /\ abs sE <= cE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     linside cW sW uW vW aW (&0) (--(&13 / &50)) /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
     ~linside cE sE uE vE aE (&1) (&0) /\
     ~linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     ldisj cW sW uW vW aW cE sE uE vE aE
     ==> sE < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    C983FSG_NONNEGATIVE_IMPOSSIBLE) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: exists_negative *)
let C983FSG_EXISTS_NEGATIVE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aE /\ aW = aE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     linside cW sW uW vW aW (--(&7 / &20)) (&7 / &20) /\
     linside cW sW uW vW aW (&0) (--(&13 / &50)) /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
     ~linside cE sE uE vE aE (&1) (&0) /\
     ~linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
     ldisj cW sW uW vW aW cE sE uE vE aE
     ==> exists cC sC uC vC aC t.
           cC * cC + sC * sC = &1 /\ &0 < aC /\ aC = aE /\
           (forall x y. linside cC sC uC vC aC x y <=> linside cE sE uE vE aE x y) /\
           &0 < cC /\ sC = --t /\ &0 < t /\ t <= cC`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aW:real = aE`)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] CLF_CANONICAL_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] THEN
  STRIP_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aE:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`]
    C983FSG_CANONICAL_NEGATIVE) THEN
  ASM_REWRITE_TAC[ldisj] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sC`] THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC);;

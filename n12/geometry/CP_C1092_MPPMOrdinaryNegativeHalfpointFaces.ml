(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOrdinaryNegativeHalfpointFaces.lean   *)
(* (N12Compact.C1092MPPMOrdinaryNegativeHalfpoint).  The literal face and    *)
(* separating-axis steps of C1092-MPPM-ORDINARY-NEGATIVE-HALFPOINT,          *)
(* sections 2 and 6.  Frame is c1092onh_frame.                                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMOrdinaryNegativeHalfpointScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/ABTransverse.ml";;

let C1092ONHF_FRAME_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c1092onh_frame x y`) o concl) ths in
    MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC (REWRITE_RULE[c1092onh_frame; REAL_POW_2] th)) ns);;

(* Lean: negative_frame *)
let C1092ONHF_NEGATIVE_FRAME = prove
 (`forall c s (u:real) (v:real) a. c * c + s * s = &1 /\ &0 < a /\ &0 < c /\ s <= &0 /\ --s <= c
     ==> c1092onh_frame c (--s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[c1092onh_frame; REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG;
    REAL_NEG_NEG] THEN ASM_REAL_ARITH_TAC);;

(* Lean: missing_face *)
let C1092ONHF_MISSING_FACE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1092onh_frame c (--s) /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&2 / &5) (--(&1)) /\
     ~linside c s u v a (&1 / &2) (--(&1))
     ==> u + a <= c / &2 - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ONHF_FRAME_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  UNDISCH_TAC `~linside c s u v a (&1 / &2) (--(&1))` THEN
  UNDISCH_TAC `linside c s u v a (&2 / &5) (--(&1))` THEN
  UNDISCH_TAC `linside c s u v a (&7 / &20) (--(&7 / &20))` THEN
  REWRITE_TAC[linside] THEN ASM_REAL_ARITH_TAC);;

(* one separating-axis case of `axes`; C = (cC,sC,uC,vC), E = (cE,sE,uE,vE), *)
(* common side aE                                                            *)
let C1092ONHF_CASE_TAC nx ny swap radius points =
  let sep = SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aE:real`;
                   `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; nx; ny]
                  ABT_SEPARATED in
  let sb ((c,s,u,v),(x,y)) =
    MP_TAC(SPECL [c; s; u; v; `aE:real`; x; y; nx; ny] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
     ASM_REAL_ARITH_TAC; STRIP_TAC] in
  MP_TAC sep THEN ANTS_TAC THENL
  [(if swap then MATCH_MP_TAC(REAL_ARITH `b + a <= x ==> a + b <= x:real`)
    else ALL_TAC) THEN
   MP_TAC radius THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MAP_EVERY sb points THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; RASM_ARITH_TAC];;

(* Lean: axes *)
let C1092ONHF_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     aC = aE /\ c1092onh_frame cC (--sC) /\ c1092onh_frame cE (--sE) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         ABT_upper cC sC uC vC aC cE sE <= uE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aC:real = aE`)) THEN
  C1092ONHF_FRAME_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aE:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aE:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`]
    CSAT_FACESEPARATION_OF_DISJOINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[C977CB_faceSep]] THEN
  let qC = (`cC:real`,`sC:real`,`uC:real`,`vC:real`)
  and qE = (`cE:real`,`sE:real`,`uE:real`,`vE:real`) in
  let src = (qC,(`--(&7 / &20)`,`--(&7 / &20)`))
  and tgt = (qE,(`&7 / &20`,`--(&7 / &20)`))
  and bar = (qE,(`&13 / &50`,`--(&1)`)) in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
  [C1092ONHF_CASE_TAC `cC:real` `sC:real` false
     (SPECL [`cC:real`; `sC:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`]
       ABT_PARALLEL_RADIUS) [src; tgt];
   C1092ONHF_CASE_TAC `--sC:real` `cC:real` false
     (SPECL [`cC:real`; `sC:real`; `aE:real`; `cE:real`; `sE:real`; `aE:real`]
       ABT_TRANSVERSE_RADIUS) [src; tgt; bar];
   C1092ONHF_CASE_TAC `cE:real` `sE:real` true
     (SPECL [`cE:real`; `sE:real`; `aE:real`; `cC:real`; `sC:real`; `aE:real`]
       ABT_PARALLEL_RADIUS) [src; tgt];
   C1092ONHF_CASE_TAC `--sE:real` `cE:real` true
     (SPECL [`cE:real`; `sE:real`; `aE:real`; `cC:real`; `sC:real`; `aE:real`]
       ABT_TRANSVERSE_RADIUS) [src; tgt; bar]]);;

(* Lean: forward_owned_caps *)
let C1092ONHF_FORWARD_OWNED_CAPS = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ c1092onh_frame c (--s) /\
     linside c s u v a (--(&1)) (--(&13 / &50)) /\
     linside c s u v a (--(&1)) (--(&2 / &5)) /\
     linside c s u v a (--(&13 / &50)) (&0) /\
     ~linside c s u v a (--(&543 / &500)) (&0) /\
     ~linside c s u v a (--(&7 / &20)) (&7 / &20)
     ==> --(&543 / &500) * c <= u /\ v + a <= (&7 / &20) * (c + s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092ONHF_FRAME_TAC THEN
  UNDISCH_TAC `~linside c s u v a (--(&7 / &20)) (&7 / &20)` THEN
  UNDISCH_TAC `~linside c s u v a (--(&543 / &500)) (&0)` THEN
  UNDISCH_TAC `linside c s u v a (--(&13 / &50)) (&0)` THEN
  UNDISCH_TAC `linside c s u v a (--(&1)) (--(&2 / &5))` THEN
  UNDISCH_TAC `linside c s u v a (--(&1)) (--(&13 / &50))` THEN
  REWRITE_TAC[linside] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN ASM_REAL_ARITH_TAC);;

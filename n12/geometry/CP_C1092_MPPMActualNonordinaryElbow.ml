(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMActualNonordinaryElbow.lean          *)
(* (N12Compact.C1092MPPMActualNonordinary).  ELBOW-EXCLUSION Lemma 1 and     *)
(* Theorem 3.  SuccessorFaces is c1092mane_successorFaces; Profile is        *)
(* c1092ep_profile; upper/lower are ABT_upper/ABT_lower; the Lean lets k, l  *)
(* are written out.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMActualNonordinaryScalars.ml";;
needs "n12/geometry/CP_C1092_ElbowProfile.ml";;

let C1092MANE_LIN = NLIN_TAC ~deg2:false [];;

let C1092MANE_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MANE_LIN; ALL_TAC];;

let C1092MANE_CONTRA = ONCE_REWRITE_TAC[GSYM REAL_NOT_LT; GSYM REAL_NOT_LE] THEN DISCH_TAC;;

let C1092MANE_MISS_TAC t =
  UNDISCH_TAC t THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> false`) THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN C1092MANE_LIN;;

let C1092MANE_UNFOLD_ALL_TAC =
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(REWRITE_RULE[linside] th))
    (filter (fun th -> can (term_match [] `linside c s u v a x y`) (concl th)) ths));;

(* Lean: SuccessorFaces (structure) *)
let c1092mane_successorFaces = new_definition
 `c1092mane_successorFaces (c:real) s u v a <=>
    --(&1 / &2) * s <= u /\ u + a <= c - s /\
    --(&543 / &500) * c <= v /\ v + a <= --s - (&2 / &5) * c`;;

(* Lean: successor_faces *)
let C1092MANE_SUCCESSOR_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ &1 < a /\ c977cc_normal c (--s) /\
     linside c s u v a (&7 / &20) (--(&7 / &20)) /\
     linside c s u v a (&13 / &50) (--(&1)) /\ linside c s u v a (&2 / &5) (--(&1)) /\
     ~linside c s u v a (&1) (--(&2 / &5)) /\ ~linside c s u v a (&1) (--(&1)) /\
     ~linside c s u v a (&0) (--(&543 / &500)) /\ ~linside c s u v a (&0) (--(&1 / &2))
     ==> c1092mane_successorFaces c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal; REAL_POW_2] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  C1092MANE_UNFOLD_ALL_TAC THEN
  REWRITE_TAC[c1092mane_successorFaces] THEN
  SUBGOAL_THEN `--(&1 / &2) * s <= u` ASSUME_TAC THENL
   [C1092MANE_CONTRA THEN C1092MANE_MISS_TAC `~linside c s u v a (&0) (--(&1 / &2))`;
    ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= --s - (&2 / &5) * c` ASSUME_TAC THENL
   [C1092MANE_CONTRA THEN C1092MANE_MISS_TAC `~linside c s u v a (&1) (--(&2 / &5))`;
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= c - s` ASSUME_TAC THENL
   [C1092MANE_CONTRA THEN C1092MANE_MISS_TAC `~linside c s u v a (&1) (--(&1))`;
    ALL_TAC] THEN
  SUBGOAL_THEN `--(&543 / &500) * c <= v` ASSUME_TAC THENL
   [C1092MANE_CONTRA THEN C1092MANE_MISS_TAC `~linside c s u v a (&0) (--(&543 / &500))`;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* the rightward claim of successor_axes *)
let C1092MANE_RIGHTWARD = prove
 (`forall cC sC uC vC aC cE sE uE vE aE nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     nx pow 2 + ny pow 2 = &1 /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     ABT_upper cC sC uC vC aC nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `--(&7 / &20)`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                `&7 / &20`; `--(&7 / &20)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN C1092MANE_LIN);;

let C1092MANE_UNIT_TAC =
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  ASM_REAL_ARITH_TAC;;

let C1092MANE_CONE_TAC rev nx ny =
  POP_ASSUM(fun th ->
    let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; nx; ny]
             C1092MANE_RIGHTWARD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[th'] THEN C1092MANE_UNIT_TAC; ALL_TAC]) THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN RASM_ARITH_TAC;;

let C1092MANE_TAKE_TAC rev =
  POP_ASSUM(fun th ->
    let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
    MP_TAC th') THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[];;

(* Lean: successor_axes *)
let C1092MANE_SUCCESSOR_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     aC = aE /\ &0 < cC /\ &0 < sC /\ &0 < cE /\ sE <= &0 /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         ABT_upper cC sC uC vC aC sC (--cC) <= ABT_lower cE sE uE vE aE sC (--cC) \/
         ABT_upper cC sC uC vC aC cE sE <= uE \/
         ABT_upper cC sC uC vC aC (--sE) cE <= vE`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [C1092MANE_TAKE_TAC false;
    C1092MANE_CONE_TAC true `--cC` `--sC`;
    C1092MANE_CONE_TAC false `--sC` `cC:real`;
    C1092MANE_TAKE_TAC true;
    C1092MANE_TAKE_TAC false;
    C1092MANE_CONE_TAC true `--cE` `--sE`;
    C1092MANE_TAKE_TAC false;
    C1092MANE_CONE_TAC true `sE:real` `--cE`]);;

(* Lean: origin_impossible *)
let C1092MANE_ORIGIN_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aC /\ aC = aE /\ c1092ep_profile cC sC uC vC aC /\ c977cc_normal cE (--sE) /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     linside cC sC uC vC aC (--(&13 / &50)) (&0) /\
     ~linside cC sC uC vC aC (--(&1)) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
     linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
     ~linside cE sE uE vE aE (&1) (--(&2 / &5)) /\ ~linside cE sE uE vE aE (&1) (--(&1)) /\
     ~linside cE sE uE vE aE (&0) (--(&543 / &500)) /\
     ldisj cC sC uC vC aC cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092ep_profile] o
    check (fun th -> can (term_match [] `c1092ep_profile c s u v a`) (concl th))) THEN
  SUBGOAL_THEN `~linside cE sE uE vE aC (&0) (--(&1 / &2))` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cC sC uC vC aC cE sE uE vE aC` THEN REWRITE_TAC[ldisj] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092MANE_SUCCESSOR_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[c1092mane_successorFaces] THEN STRIP_TAC] THEN
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; REAL_POW_2] th)) ns) THEN
  SUBGOAL_THEN `&0 < cC /\ &0 < cE` STRIP_ASSUME_TAC THENL [CONJ_TAC THEN C1092MANE_LIN; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] C1092MANE_SUCCESSOR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092MANE_LIN; DISCH_TAC] THEN
  C1092MANE_UNFOLD_ALL_TAC THEN
  SUBGOAL_THEN `vC + aC <= sC` ASSUME_TAC THENL
   [C1092MANE_CONTRA THEN C1092MANE_MISS_TAC `~linside cC sC uC vC aC (--(&1)) (&0)`; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] C1092MANS_RELATIVE_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092MANE_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) + (--cC * sE + sC * cE))` THEN
  FIRST_X_ASSUM(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [(* own *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                  `cC * cE + sC * sE`; `--cC * sE + sC * cE`] C1092WS_LOWER_NN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092MANE_LIN); DISCH_TAC] THEN
    C1092MANE_PROD `&0 <= (cC * cE + sC * sE) * (cE - sE - aC - uE)` THEN
    C1092MANE_PROD `&0 <= (--cC * sE + sC * cE) * (--sE - (&2 / &5) * cE - aC - vE)` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] C1092MANS_SOURCE_LONGITUDINAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MANE_LIN;
    (* transverse *)
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `sC:real`; `--cC:real`;
                  `--cC * sE + sC * cE`; `--(cC * cE + sC * sE)`] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092MANE_LIN); DISCH_TAC] THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sC:real`; `cC:real`]
      C1092TFSU_UPPER_NEG) THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
    ASM_REWRITE_TAC[REAL_NEG_NEG] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    C1092MANE_PROD `&0 <= (--cC * sE + sC * cE) * (cE - sE - aC - uE)` THEN
    C1092MANE_PROD `&0 <= (cC * cE + sC * sE) * (vE + (&543 / &500) * cE)` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] C1092MANS_SOURCE_TRANSVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MANE_LIN;
    (* neighbor *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `cE:real`; `sE:real`;
                  `cC * cE + sC * sE`; `--(--cC * sE + sC * cE)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092MANE_LIN); DISCH_TAC] THEN
    C1092MANE_PROD `&0 <= (cC * cE + sC * sE) * (uC + cC + (&2 / &5) * sC)` THEN
    C1092MANE_PROD `&0 <= (--cC * sE + sC * cE) * (sC - aC - vC)` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] C1092MANS_SUCCESSOR_LONGITUDINAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MANE_LIN;
    (* neighborV *)
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `--sE:real`; `cE:real`;
                  `--cC * sE + sC * cE`; `cC * cE + sC * sE`] C1092TFSU_UPPER_POS_POS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
      (REAL_ARITH_TAC ORELSE C1092MANE_LIN); DISCH_TAC] THEN
    C1092MANE_PROD `&0 <= (--cC * sE + sC * cE) * (uC + cC + (&2 / &5) * sC)` THEN
    C1092MANE_PROD `&0 <= (cC * cE + sC * sE) * (vC + cC - (&2 / &5) * sC)` THEN
    MP_TAC(SPECL [`cC:real`; `sC:real`; `cE:real`; `--sE:real`] C1092MANS_SUCCESSOR_TRANSVERSE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN C1092MANE_LIN]);;

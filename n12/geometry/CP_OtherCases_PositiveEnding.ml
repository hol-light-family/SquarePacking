(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/PositiveEnding.lean                *)
(* (N12Compact.Completion.OtherCases.PositiveEnding).  The complete positive *)
(* southeast ending over the two original physical squares.                 *)
(* W = (cW,sW,uW,vW,aW), E = (cE,sE,uE,vE,aE) (unit normals / positive sides *)
(* explicit); upper / lower = ABT_upper / ABT_lower, strict_bounds =         *)
(* ABT_STRICT_BOUNDS, WallProfile.upper_neg / lower_neg = OCWPVG_*_NEG,      *)
(* PositiveEndingFaces.faces / Data = OCPEF_FACES / ocpef_data,              *)
(* ClosedFrames.canonical_frame = CLF_CANONICAL_FRAME, PositiveEndingSupports*)
(* own_axis / negative_w_axis / positive_w_axis = OCPESU_*;                  *)
(* faceSeparation_of_disjoint + separated + radii = ABT_FOUR_AXES.  The      *)
(* local `cone` and `reverse` of the Lean proof are OCPEND_CONE /            *)
(* OCPEND_REVERSE.  Tag OCPEND_.                                             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_PositiveEndingSupports.ml";;
needs "n12/geometry/ClosedFrames.ml";;

let OCPEND_LIN = NLIN_TAC ~deg2:false [];;

(* local cone of impossible (for the canonical frame w of W) *)
let OCPEND_CONE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE nx ny.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     ocpef_data cE sE uE vE aE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\ linside cW sW uW vW aW (&0) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cW sW uW vW aW nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx /\ ny < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  OCPESU_DATA_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `--(&7 / &20)`; `--(&7 / &20)`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `&0`; `&0`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `&7 / &20`; `--(&7 / &20)`;
                `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `&0`;
                `--(C1092WPS_half cE sE)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ny < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= ny * C1092WPS_half cE sE` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN OCPEND_LIN; ALL_TAC] THEN
    OCPEND_LIN;
    ASM_REWRITE_TAC[] THEN OCPEND_LIN]);;

(* local reverse of impossible *)
let OCPEND_REVERSE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE nx ny.
     ABT_upper cE sE uE vE aE nx ny <= ABT_lower cW sW uW vW aW nx ny
     ==> ABT_upper cW sW uW vW aW (--nx) (--ny) <= ABT_lower cE sE uE vE aE (--nx) (--ny)`,
  REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN REAL_ARITH_TAC);;

(* Lean: impossible *)
let OCPEND_IMPOSSIBLE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aE /\ aW = aE /\ aW <= &1001 / &1000 /\
     &0 < cE /\ &0 < sE /\ sE <= cE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
     ~linside cE sE uE vE aE (&1) (&0) /\ ~linside cE sE uE vE aE (&21 / &40) (&1 / &8) /\
     (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside cE sE uE vE aE x (--(&1))) /\
     (forall y. &0 <= y ==> y <= &4 / &5 ==> ~linside cW sW uW vW aW (--(&1)) y) /\
     ldisj cW sW uW vW aW cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] OCPEF_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  OCPESU_DATA_TAC THEN
  MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] CLF_CANONICAL_FRAME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cw:real` (X_CHOOSE_THEN `sw:real` (X_CHOOSE_THEN `uw:real`
    (X_CHOOSE_THEN `vw:real` (X_CHOOSE_THEN `aw:real` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `linside cw sw uw vw aw (--(&7 / &20)) (--(&7 / &20)) /\
                linside cw sw uw vw aw (&0) (&0) /\
                (forall y. &0 <= y ==> y <= &4 / &5 ==> ~linside cw sw uw vw aw (--(&1)) y)`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ldisj cw sw uw vw aw cE sE uE vE aE` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cW sW uW vW aW cE sE uE vE aE` THEN ASM_REWRITE_TAC[ldisj]; ALL_TAC] THEN
  SUBGOAL_THEN `~linside cw sw uw vw aw (&0) (--(C1092WPS_half cE sE))` ASSUME_TAC THENL
   [UNDISCH_TAC `ldisj cW sW uW vW aW cE sE uE vE aE` THEN REWRITE_TAC[ldisj] THEN
    DISCH_THEN(MP_TAC o SPECL [`&0`; `--(C1092WPS_half cE sE)`]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 < aw /\ aw <= &1001 / &1000 /\ aw = aE /\ abs sw <= cw` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  (* forget the original W *)
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    let t = concl th in is_forall t && is_iff (snd (strip_forall t))))) THEN
  let tW = [`cw:real`; `sw:real`; `uw:real`; `vw:real`; `aw:real`]
  and tE = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] in
  let cone nx ny =
    MP_TAC(SPECL (tW @ tE @ [nx; ny]) OCPEND_CONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
      STRIP_TAC THEN RASM_ARITH_TAC] in
  let side th extra =
    MP_TAC(SPECL (tW @ tE @ extra) th) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT CONJ_TAC THEN
      FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; RASM_ARITH_TAC];
      REWRITE_TAC[]] in
  MP_TAC(SPECL (tW @ tE) ABT_FOUR_AXES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST_ASSUM(fun th -> ASSUME_TAC(REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP OCPEND_REVERSE th))) THEN
  ASM_CASES_TAC `&0 <= sw` THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  FIRST [cone `cw:real` `sw:real`; cone `--cw` `--sw`; cone `--sw` `cw:real`;
         cone `sw:real` `--cw`; cone `cE:real` `sE:real`; cone `--cE` `--sE`;
         cone `--sE` `cE:real`;
         side OCPESU_NEGATIVE_W_AXIS [`--sw`];
         side OCPESU_POSITIVE_W_AXIS [];
         side OCPESU_OWN_AXIS []]);;

(* Lean: nonnegative_impossible *)
let OCPEND_NONNEGATIVE_IMPOSSIBLE = prove
 (`forall cW sW uW vW aW cE sE uE vE aE.
     cW * cW + sW * sW = &1 /\ &0 < aW /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     &1 < aE /\ aW = aE /\ aW <= &1001 / &1000 /\
     &0 < cE /\ &0 <= sE /\ sE <= cE /\
     linside cW sW uW vW aW (--(&7 / &20)) (--(&7 / &20)) /\
     linside cW sW uW vW aW (&0) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&13 / &50) (&0) /\
     linside cE sE uE vE aE (&1) (--(&13 / &50)) /\
     ~linside cE sE uE vE aE (&1) (&0) /\ ~linside cE sE uE vE aE (&21 / &40) (&1 / &8) /\
     (forall x. &13 / &50 <= x ==> x <= &4 / &5 ==> ~linside cE sE uE vE aE x (--(&1))) /\
     (forall y. &0 <= y ==> y <= &4 / &5 ==> ~linside cW sW uW vW aW (--(&1)) y) /\
     ldisj cW sW uW vW aW cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `&0 < sE` THENL
   [MP_TAC(SPECL [`cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] OCPEND_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sE = &0` SUBST_ALL_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`~linside cE (&0) uE vE aE (&1) (&0)`;
                         `linside cE (&0) uE vE aE (&1) (--(&13 / &50))`;
                         `linside cE (&0) uE vE aE (&13 / &50) (&0)`] THEN
  REWRITE_TAC[linside] THEN UNDISCH_TAC `&0 < cE` THEN REAL_ARITH_TAC);;

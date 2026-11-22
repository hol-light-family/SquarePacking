(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMSteepPositiveThreeSquareData.lean    *)
(* (namespace N12Compact.C1092MPPMSteepPositiveThreeSquare).  Literal        *)
(* three-square input and the directed normal sources of                     *)
(* STEEP-POSITIVE-THREE-SQUARE-REDUCTION, sections 1--2.                     *)
(* Squares C, E, B are (cC, ..), (cE, ..), (cB, ..).  Input: c1092spts_input;*)
(* Quarter: c1092mcs_quarter; lower/upper: ABT_lower/ABT_upper; reverse:     *)
(* C1092TFSU_REVERSE; lower_nn: C1092WS_LOWER_NN; the SAT axes:              *)
(* ABT_FOUR_AXES (CongruentSAT.faceSeparation_of_disjoint + separated).      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMCrosspointSupportScalars.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;
needs "n12/geometry/CP_C1092_ShallowBoundarySupport.ml";;

(* Lean: Input (structure) *)
let c1092spts_input = new_definition
 `c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB <=>
    &1 < aC /\ aC = aE /\ aC = aB /\ c977cc_normal cC sC /\ c977cc_normal cE sE /\
    &3 / &5 <= sC /\ --cC - sC <= uC /\ uC + aC <= --cC / &2 /\
    vC + aC <= (&543 / &500) * sC /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
    uE + aE <= cE - (&14 / &25) * sE /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    linside cE sE uE vE aE (&0) (--(&1 / &2)) /\
    linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
    linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
    linside cB sB uB vB aB (&0) (--(&1)) /\
    (forall x y. linside cB sB uB vB aB x y ==> --(&2) <= y) /\
    ldisj cB sB uB vB aB cC sC uC vC aC /\
    ldisj cB sB uB vB aB cE sE uE vE aE`;;

let C1092SPTS_LIN_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (fun g -> if is_eq(snd g) then REAL_ARITH_TAC g else NLIN_TAC ~deg2:false [] g));;

(* Lean: signed_axes *)
let C1092SPTS_SIGNED_AXES = prove
 (`forall cB sB uB vB aB cQ sQ uQ vQ aQ.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cQ * cQ + sQ * sQ = &1 /\ &0 < aQ /\
     aB = aQ /\ ldisj cB sB uB vB aB cQ sQ uQ vQ aQ
     ==> ABT_upper cB sB uB vB aB cB sB <= ABT_lower cQ sQ uQ vQ aQ cB sB \/
         ABT_upper cB sB uB vB aB (--cB) (--sB) <= ABT_lower cQ sQ uQ vQ aQ (--cB) (--sB) \/
         ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cQ sQ uQ vQ aQ (--sB) cB \/
         ABT_upper cB sB uB vB aB sB (--cB) <= ABT_lower cQ sQ uQ vQ aQ sB (--cB) \/
         ABT_upper cB sB uB vB aB cQ sQ <= ABT_lower cQ sQ uQ vQ aQ cQ sQ \/
         ABT_upper cB sB uB vB aB (--cQ) (--sQ) <= ABT_lower cQ sQ uQ vQ aQ (--cQ) (--sQ) \/
         ABT_upper cB sB uB vB aB (--sQ) cQ <= ABT_lower cQ sQ uQ vQ aQ (--sQ) cQ \/
         ABT_upper cB sB uB vB aB sQ (--cQ) <= ABT_lower cQ sQ uQ vQ aQ sQ (--cQ)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cQ:real`; `sQ:real`; `uQ:real`; `vQ:real`; `aQ:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    if is_real_rel(concl th) && can (find_term (fun t -> try fst(dest_const(fst(strip_comb t)))
         = "ABT_upper" with _ -> false)) (concl th)
    then ASSUME_TAC th THEN
         ASSUME_TAC(REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th))
    else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

(* Lean: anchor_cone *)
let C1092SPTS_ANCHOR_CONE = prove
 (`forall cC sC uC vC aC cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cB sB uB vB aB nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < ny /\ nx < (&413 / &500) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&7 / &20)`,`--(&7 / &20)`);
    [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`], (`--(&1)`,`--(&13 / &50)`);
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`], (`&0`,`--(&543 / &500)`);
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`], (`--(&2 / &5)`,`--(&1)`)] THEN
  C1092SPTS_LIN_TAC);;

let C1092SPTS_UNPACK_TAC =
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spts_input] o
    check (can (term_match [] `c1092spts_input a b c d e f g h i j k l m n o'`) o concl));;

(* Lean: central_cone *)
let C1092SPTS_CENTRAL_CONE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cB sB uB vB aB nx ny <= ABT_lower cC sC uC vC aC nx ny
     ==> &0 < ny /\ nx < (&413 / &500) * ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SPTS_UNPACK_TAC THEN
  MATCH_MP_TAC C1092SPTS_ANCHOR_CONE THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  ASM_REWRITE_TAC[]);;

(* Lean: recipient_cone *)
let C1092SPTS_RECIPIENT_CONE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     nx pow 2 + ny pow 2 = &1 /\
     ABT_upper cB sB uB vB aB nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx /\ &0 < ny`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SPTS_UNPACK_TAC THEN
  MAP_EVERY (fun (sq,(x,y)) ->
      MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`], (`&2 / &5`,`--(&1)`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`], (`&0`,`--(&1 / &2)`);
    [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`], (`&0`,`--(&1)`)] THEN
  C1092SPTS_LIN_TAC);;

(* Lean: northeast_of_faces *)
let C1092SPTS_NORTHEAST_OF_FACES = prove
 (`forall cC sC uC vC aC cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     &1 < aC /\ c977cc_normal cC sC /\ &0 < sC /\
     uC + aC <= --cC / &2 /\ vC + aC <= (&543 / &500) * sC /\
     linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
     linside cC sC uC vC aC (--(&1)) (--(&13 / &50)) /\
     linside cB sB uB vB aB (&0) (--(&543 / &500)) /\
     linside cB sB uB vB aB (--(&2 / &5)) (--(&1)) /\
     nx pow 2 + ny pow 2 = &1 /\ &0 <= nx /\ &0 <= ny
     ==> ~(ABT_upper cB sB uB vB aB nx ny <= ABT_lower cC sC uC vC aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC_ALL C1092SPTS_ANCHOR_CONE) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `c977cc_normal x y`) (concl th) then
    STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) else NO_TAC) THEN
  let u = `nx * cC + ny * sC` and v = `--nx * sC + ny * cC` in
  let add x y = mk_comb(mk_comb(`(+):real->real->real`,x),y) in
  MP_TAC(SPECL [`nx:real`; `cC:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`ny:real`; `sC:real`] REAL_LE_MUL) THEN
  MP_TAC(SPECL [`ny:real`; `sC:real`; `cC:real`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`sC:real`; `ny - nx`] REAL_LT_MUL) THEN
  REPEAT(ANTS_TAC THENL [C1092SPTS_LIN_TAC; DISCH_TAC]) THEN
  SUBGOAL_THEN (mk_conj(mk_comb(mk_comb(`(<=):real->real->bool`,`&0`),u),
                        mk_comb(mk_comb(`(<):real->real->bool`,`&0`),v))) STRIP_ASSUME_TAC THENL
   [C1092SPTS_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `nx:real`; `ny:real`;
                u; v] C1092WS_LOWER_NN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C1092SPTS_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [u; `uC + aC`; `--cC / &2`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [v; `vC + aC`; `(&543 / &500) * sC`] REAL_LE_LMUL) THEN
  MP_TAC(SPECL [`aC - &1`; add u v] REAL_LE_MUL) THEN
  REPEAT(ANTS_TAC THENL [C1092SPTS_LIN_TAC; DISCH_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `--(&1 / &10) - cC + sC - (&293 / &500) * sC * sC < &0` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `sC:real`]; ALL_TAC] THEN
  SUBGOAL_THEN `(&14 / &17) * cC * sC <= cC + sC - &1` ASSUME_TAC THENL
   [MP_TAC(SPECL [`cC + sC - &1`; `&17 / &7 - (cC + sC + &1)`] REAL_LE_MUL) THEN
    ANTS_TAC THENL [C1092SPTS_LIN_TAC; DISCH_TAC] THEN C1092SPTS_LIN_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] REAL_LT_MUL) THEN
  ANTS_TAC THENL [C1092SPTS_LIN_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `&1 - cC - sC + (&293 / &500) * cC * sC < &0` ASSUME_TAC THENL
   [C1092SPTS_LIN_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`nx:real`; `--(--(&1 / &10) - cC + sC - (&293 / &500) * sC * sC)`]
    REAL_LE_MUL) THEN
  MP_TAC(SPECL [`ny:real`; `--(&1 - cC - sC + (&293 / &500) * cC * sC)`] REAL_LT_MUL) THEN
  REPEAT(ANTS_TAC THENL [C1092SPTS_LIN_TAC; DISCH_TAC]) THEN
  SUBGOAL_THEN `nx * (cC * cC + sC * sC) = nx` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `--(&2 / &5)`; `--(&1)`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[REAL_POW_2] THEN STRIP_TAC THEN
  C1092SPTS_LIN_TAC);;

(* Lean: northeast_impossible *)
let C1092SPTS_NORTHEAST_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB nx ny.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     nx pow 2 + ny pow 2 = &1 /\ &0 <= nx /\ &0 <= ny
     ==> ~(ABT_upper cB sB uB vB aB nx ny <= ABT_lower cC sC uC vC aC nx ny)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C1092SPTS_UNPACK_TAC THEN
  MATCH_MP_TAC C1092SPTS_NORTHEAST_OF_FACES THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* the eight signed cases of signed_axes; cone : nx -> ny -> thm, ne : thm *)
let C1092SPTS_CASE_TAC cone ne facts =
  FIRST
   [ASM_REWRITE_TAC[] THEN NO_TAC;
    MP_TAC ne THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    FIRST_X_ASSUM(fun th ->
      if is_real_rel(concl th) &&
         (try fst(dest_const(fst(strip_comb(lhand(concl th))))) = "ABT_upper"
          with _ -> false)
      then (let args = snd(strip_comb(lhand(concl th))) in
            MP_TAC(cone (el 5 args) (el 6 args)) THEN ASM_REWRITE_TAC[th] THEN
            MP_TAC facts THEN REAL_ARITH_TAC)
      else NO_TAC)];;

(* Lean: central_sources *)
let C1092SPTS_CENTRAL_SOURCES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB
     ==> ABT_upper cB sB uB vB aB (--sC) cC <= vC \/
         ABT_upper cB sB uB vB aB (--sB) cB <= ABT_lower cC sC uC vC aC (--sB) cB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spts_input] o
    check (can (term_match [] `c1092spts_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter x y`) o concl)) THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNV) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  let facts = REWRITE_RULE[c977cc_normal]
    (CONJ (end_itlist CONJ (map ASSUME [`&0 <= cB`; `&0 <= sB`; `cB pow 2 + sB pow 2 = &1`]))
     (CONJ (ASSUME `c977cc_normal cC sC`) (ASSUME `&7 / &10 <= cC`))) in
  let ne = SPECL [`cB:real`; `sB:real`]
    (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
            `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
            `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092SPTS_NORTHEAST_IMPOSSIBLE) in
  let cone nx ny = SPECL [nx; ny]
    (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
            `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
            `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092SPTS_CENTRAL_CONE) in
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C1092SPTS_SIGNED_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092SPTS_CASE_TAC cone ne facts);;

(* Lean: recipient_sources *)
let C1092SPTS_RECIPIENT_SOURCES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092spts_input cC sC uC vC aC cE sE uE vE aE cB sB uB vB aB /\
     c1092mcs_quarter cB sB
     ==> ABT_upper cB sB uB vB aB cE sE <= uE \/
         ABT_upper cB sB uB vB aB cB sB <= ABT_lower cE sE uE vE aE cB sB`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092spts_input] o
    check (can (term_match [] `c1092spts_input a b c d e f g h i j k l m n o'`) o concl)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mcs_quarter] o
    check (can (term_match [] `c1092mcs_quarter x y`) o concl)) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`] C977CC_NORMAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNU) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  let facts = REWRITE_RULE[c977cc_normal]
    (CONJ (end_itlist CONJ (map ASSUME [`&0 <= cB`; `&0 <= sB`; `cB pow 2 + sB pow 2 = &1`]))
     (CONJ (ASSUME `c977cc_normal cE sE`) (ASSUME `&7 / &10 <= cE`))) in
  let cone nx ny = SPECL [nx; ny]
    (SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
            `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
            `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C1092SPTS_RECIPIENT_CONE) in
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] C1092SPTS_SIGNED_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  C1092SPTS_CASE_TAC cone TRUTH facts);;

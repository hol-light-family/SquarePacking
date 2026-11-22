(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMInwardFinalSign.lean                 *)
(* (namespace N12Compact.C1092MPPMInwardFinal).  NEGATIVE-INWARD-SUCCESSOR- *)
(* SIGN Theorem 1.  Squares C = (cC, sC, uC, vC, aC), E = (cE, sE, uE, vE,  *)
(* aE); SignInput is the predicate c1092mifs_signInput; upper / lower:      *)
(* ABT_upper / ABT_lower; strict_bounds: ABT_STRICT_BOUNDS; ownU / ownV:     *)
(* ABT_OWNU / ABT_OWNV; faceSeparation_of_disjoint: ABT_FOUR_AXES;          *)
(* reverse: C1092TFSU_REVERSE; lower_pn: C1092WS_LOWER_PN; upper_pos_neg:   *)
(* C1092TFSU_UPPER_POS_NEG; NonnegativeRecipient.faces: C1092MINF_FACES;    *)
(* signFirst / signLast and their positivity: c1092mifsg_* / C1092MIFSG_*.  *)
(* Tag C1092MIFS_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMInwardNonnegativeFaces.ml";;
needs "n12/geometry/CP_C1092_TwoFifthsSupport.ml";;

(* Lean: SignInput (structure) *)
let c1092mifs_signInput = new_definition
 `c1092mifs_signInput cC sC uC vC aC cE sE uE vE aE <=>
    &1 < aC /\ aC = aE /\ c977cc_normal cC (--sC) /\
    aC - cC - (&13 / &50) * sC <= uC + aC /\
    vC + aC <= (&7 / &20) * (cC + sC) /\
    linside cC sC uC vC aC (--(&7 / &20)) (--(&7 / &20)) /\
    linside cC sC uC vC aC (&0) (--(&13 / &50)) /\
    linside cC sC uC vC aC (--(&1 / &2)) (&0) /\
    linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
    linside cE sE uE vE aE (&13 / &50) (--(&1)) /\
    linside cE sE uE vE aE (&2 / &5) (--(&1)) /\
    linside cE sE uE vE aE (&1 / &2) (--(&1)) /\
    ~linside cE sE uE vE aE (&0) (--(&13 / &50)) /\
    ~linside cE sE uE vE aE (&1) (--(&2 / &5)) /\
    ~linside cE sE uE vE aE (&0) (--(&543 / &500)) /\
    ~linside cE sE uE vE aE (&1) (--(&1)) /\
    ~linside cE sE uE vE aE (&1) (--(&543 / &500)) /\
    ldisj cC sC uC vC aC cE sE uE vE aE`;;

let C1092MIFS_LIN = REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE NLIN_TAC ~deg2:false []);;

let C1092MIFS_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   C1092MIFS_LIN; ALL_TAC];;

(* Lean: nonnegative_successor_faces *)
let C1092MIFS_NONNEGATIVE_SUCCESSOR_FACES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092mifs_signInput cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE sE
     ==> uE + aE <= cE - (&2 / &5) * sE /\ vE + aE <= --(&13 / &50) * cE /\
         --cE - sE <= vE`,
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mifs_signInput] THEN STRIP_TAC THEN
  MATCH_MP_TAC C1092MINF_FACES THEN
  ASM_REWRITE_TAC[c1092minf_data] THEN ASM_MESON_TAC[]);;

(* the directional consequence of a separation (Lean local rightward / downward) *)
let C1092MIFS_DIRECTION = prove
 (`forall cA sA uA vA aA cR sR uR vR aR x1 y1 x2 y2 nx ny.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     nx pow 2 + ny pow 2 = &1 /\ linside cA sA uA vA aA x1 y1 /\
     linside cR sR uR vR aR x2 y2 /\
     ABT_upper cA sA uA vA aA nx ny <= ABT_lower cR sR uR vR aR nx ny
     ==> nx * x1 + ny * y1 < nx * x2 + ny * y2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
                `x1:real`; `y1:real`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                `x2:real`; `y2:real`; `nx:real`; `ny:real`] ABT_STRICT_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let C1092MIFS_UNIT_TAC =
  REWRITE_TAC[REAL_POW_2; REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
  ASM_REAL_ARITH_TAC;;

(* the newest case hypothesis (optionally reversed) contradicts a direction *)
let C1092MIFS_CONE_TAC rev nx ny (x1,y1) (x2,y2) =
  POP_ASSUM(fun th ->
    let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`;
                  x1; y1; x2; y2; nx; ny] C1092MIFS_DIRECTION) THEN
    ASM_REWRITE_TAC[th']) THEN
  ANTS_TAC THENL [C1092MIFS_UNIT_TAC; ALL_TAC] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_TAC THEN MATCH_MP_TAC(TAUT `false ==> p`) THEN C1092MIFS_LIN;;

let C1092MIFS_TAKE_TAC rev =
  POP_ASSUM(fun th ->
    let th' = if rev then REWRITE_RULE[REAL_NEG_NEG] (MATCH_MP C1092TFSU_REVERSE th) else th in
    MP_TAC th') THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[];;

let C1092MIFS_INTRO_TAC =
  REPEAT GEN_TAC THEN REWRITE_TAC[c1092mifs_signInput] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (can (term_match [] `c977cc_normal x y`) o concl) ths));;

(* Lean: sign_axes (private) *)
let C1092MIFS_SIGN_AXES = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092mifs_signInput cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE sE
     ==> uC + aC <= ABT_lower cE sE uE vE aE cC sC \/
         ABT_upper cC sC uC vC aC cE sE <= uE \/
         ABT_upper cC sC uC vC aC sE (--cE) <= --(vE + aE)`,
  C1092MIFS_INTRO_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`]
    C1092TFSU_LOWER_OPPOSITE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [C1092MIFS_TAKE_TAC false;
    C1092MIFS_CONE_TAC true `--cC` `--sC`
      (`--(&7 / &20)`, `--(&7 / &20)`) (`&7 / &20`, `--(&7 / &20)`);
    C1092MIFS_CONE_TAC false `--sC` `cC:real`
      (`--(&1 / &2)`, `&0`) (`&1 / &2`, `--(&1)`);
    C1092MIFS_CONE_TAC true `sC:real` `--cC`
      (`--(&7 / &20)`, `--(&7 / &20)`) (`&7 / &20`, `--(&7 / &20)`);
    C1092MIFS_TAKE_TAC false;
    C1092MIFS_CONE_TAC true `--cE` `--sE`
      (`--(&7 / &20)`, `--(&7 / &20)`) (`&7 / &20`, `--(&7 / &20)`);
    C1092MIFS_CONE_TAC false `--sE` `cE:real`
      (`--(&7 / &20)`, `--(&7 / &20)`) (`&7 / &20`, `--(&7 / &20)`);
    C1092MIFS_TAKE_TAC true]);;

(* Lean: nonnegative_successor_impossible *)
let C1092MIFS_NONNEGATIVE_SUCCESSOR_IMPOSSIBLE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092mifs_signInput cC sC uC vC aC cE sE uE vE aE /\ c977cc_normal cE sE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092MIFS_NONNEGATIVE_SUCCESSOR_FACES) THEN
  MP_TAC(SPEC_ALL C1092MIFS_SIGN_AXES) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `sE:real`] C1092MIFSG_SIGN_FIRST_POSITIVE) THEN
  MP_TAC(SPECL [`cC:real`; `--sC`; `cE:real`; `sE:real`] C1092MIFSG_SIGN_LAST_POSITIVE) THEN
  UNDISCH_TAC `c1092mifs_signInput cC sC uC vC aC cE sE uE vE aE` THEN
  REWRITE_TAC[c1092mifs_signInput] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aC:real = aE`)) THEN
  ASSUM_LIST(fun ths -> MAP_EVERY (fun th ->
      STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th))
    (filter (can (term_match [] `c977cc_normal x y`) o concl) ths)) THEN
  DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `&0 < sE` ASSUME_TAC THENL [C1092MIFS_LIN; ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if is_imp(concl th) && lhand(concl th) = `&0 < sE`
    then ASSUME_TAC(MP th (ASSUME `&0 < sE`)) else NO_TAC) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[c1092mifsg_signFirst; c1092mifsg_signLast]) THEN
  SUBGOAL_THEN `&0 <= cC * cE + sC * sE /\ &0 <= cC * sE - sC * cE` STRIP_ASSUME_TAC THENL
   [C1092MIFS_PROD `&0 <= (cC + sC) * cE` THEN
    C1092MIFS_PROD `&0 <= --sC * (cE - sE)` THEN
    C1092MIFS_PROD `&0 <= cC * sE` THEN
    C1092MIFS_PROD `&0 <= --sC * cE` THEN
    C1092MIFS_LIN;
    ALL_TAC] THEN
  C1092MIFS_PROD `&0 < (aC - &1) * (&1 + (cC * cE + sC * sE) + (cC * sE - sC * cE))` THEN
  FIRST_X_ASSUM(fun th -> if is_disj(concl th) then
    DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC) th else NO_TAC) THENL
   [MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aC:real`; `cC:real`; `sC:real`;
                  `cC * cE + sC * sE`; `--(cC * sE - sC * cE)`] C1092WS_LOWER_PN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    C1092MIFS_PROD `&0 <= (cC * cE + sC * sE) * (cE - (&2 / &5) * sE - aC - uE)` THEN
    C1092MIFS_PROD `&0 <= (cC * sE - sC * cE) * (vE + cE + sE)` THEN
    C1092MIFS_LIN;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                  `&0`; `--(&13 / &50)`; `cE:real`; `sE:real`] ABT_STRICT_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_POW_2] THEN ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
    C1092MIFS_LIN;
    MP_TAC(SPECL [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`; `sE:real`; `--cE`;
                  `cC * sE - sC * cE`; `--(cC * cE + sC * sE)`] C1092TFSU_UPPER_POS_NEG) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC] THEN
    C1092MIFS_PROD `&0 <= (cC * sE - sC * cE) * (uC + cC + (&13 / &50) * sC)` THEN
    C1092MIFS_PROD `&0 <= (cC * cE + sC * sE) * ((&7 / &20) * (cC + sC) - vC - aC)` THEN
    C1092MIFS_LIN]);;

(* Lean: successor_negative *)
let C1092MIFS_SUCCESSOR_NEGATIVE = prove
 (`forall cC sC uC vC aC cE sE uE vE aE.
     cC * cC + sC * sC = &1 /\ &0 < aC /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     c1092mifs_signInput cC sC uC vC aC cE sE uE vE aE /\ abs sE <= cE
     ==> sE < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MATCH_MP_TAC C1092MIFS_NONNEGATIVE_SUCCESSOR_IMPOSSIBLE THEN
  MAP_EVERY EXISTS_TAC [`cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`;
                        `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] THEN
  ASM_REWRITE_TAC[c977cc_normal] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
  UNDISCH_TAC `cE * cE + sE * sE = &1` THEN REWRITE_TAC[REAL_POW_2]);;

(* ========================================================================= *)
(* Port of Compact/Geometry/C849Positive.lean (N12Compact.C849Positive).     *)
(* Complete positive canonical-B sector for the 849/851 geometry.            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C849ShallowAB.ml";;

(* Lean: right_cap *)
let C849P_RIGHT_CAP = prove
 (`forall cB sB uB vB aB cC sC uC vC aC.
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     linside cC sC uC vC aC (&113 / &50) (&3) /\
     ldisj cB sB uB vB aB cC sC uC vC aC
     ==> uB + aB <= (&113 / &50) * cB + &3 * sB`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ldisj] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`&113 / &50`; `&3`]) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[TAUT `(~p ==> false) <=> p`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside]) THEN REWRITE_TAC[linside] THEN
  REPEAT CONJ_TAC THEN C849SHAB_LIN_TAC);;

(* the steep/shallow split shared by impossible and MTFG positive_impossible *)
let C849P_SPLIT = prove
 (`forall c s. c * c + s * s = &1 /\ &0 <= s /\ &0 < c /\ &50 / &63 < c
         ==> s <= (&4 / &5) * c`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 < (s - (&4 / &5) * c) * (s + (&4 / &5) * c)`;
    `&0 < (c - &50 / &63) * (c + &50 / &63)`] THEN
  NLIN_TAC []);;

(* Lean: impossible *)
let C849P_IMPOSSIBLE = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cR sR uR vR aR cC sC uC vC aC cE sE uE vE aE.
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cB * cB + sB * sB = &1 /\ &0 < aB /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     &0 < cB /\ &0 <= sB /\ sB <= cB /\
     aA = aB /\ &1 < aB /\ &1 < aR /\
     lcont cR sR uR vR aR /\
     lclosed cA sA uA vA aA (&2) (&113 / &50) /\
     lclosed cA sA uA vA aA (&113 / &50) (&2) /\
     linside cA sA uA vA aA (&47 / &20) (&47 / &20) /\
     ~linside cA sA uA vA aA (&33 / &20) (&33 / &20) /\
     ~linside cA sA uA vA aA (&47 / &20) (&33 / &20) /\
     lclosed cB sB uB vB aB (&33 / &20) (&47 / &20) /\
     lclosed cB sB uB vB aB (&8 / &5) (&3) /\
     linside cB sB uB vB aB (&2) (&1543 / &500) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     lclosed cR sR uR vR aR (&1543 / &500) (&2) /\
     ~linside cR sR uR vR aR (&81 / &25) (&187 / &100) /\
     linside cC sC uC vC aC (&113 / &50) (&3) /\
     linside cE sE uE vE aE (&1) (&3) /\
     ldisj cA sA uA vA aA cB sB uB vB aB /\
     ldisj cA sA uA vA aA cR sR uR vR aR /\
     ldisj cB sB uB vB aB cC sC uC vC aC /\
     ldisj cB sB uB vB aB cE sE uE vE aE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `aA:real = aB`)) THEN
  MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] FSAA_POINT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[LINSIDE_CLOSED] THEN C849SHAB_LIN_TAC; DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C849PA_B_LOWER_FACE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    DISCH_TAC THEN UNDISCH_TAC `ldisj cA sA uA vA aB cB sB uB vB aB` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&2`; `&5 / &2`]) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    PBLR_UPPER_LEFT_MARKER_MODES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN TRY C849SHAB_LIN_TAC THEN
    DISCH_TAC THEN UNDISCH_TAC `ldisj cB sB uB vB aB cE sE uE vE aE` THEN
    REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&1`; `&3`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cC:real`; `sC:real`; `uC:real`; `vC:real`; `aC:real`] C849P_RIGHT_CAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cB:real`; `sB:real`] C849P_SPLIT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C849SHAB_LIN_TAC; DISCH_TAC] THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `&33 / &20`; `&47 / &20`] OUTSIDE_OF_CLOSED) THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                  `&3`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
    ASM_REWRITE_TAC[GSYM ldisj] THEN REPEAT DISCH_TAC THEN
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`]
      CLF_POSITIVE_FRAME) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`] THEN
    STRIP_TAC THEN
    MP_TAC(SPECL [`c':real`; `s':real`; `u':real`; `v':real`; `a':real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] C849SHAB_IN_FRAME) THEN
    SUBGOAL_THEN `&3 * cB <= &7 * sB` ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[lclosed]) THEN C849SHAB_LIN_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ldisj] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aB:real`;
                  `cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] C849SAB_IMPOSSIBLE) THEN
    ASM_SIMP_TAC[]]);;

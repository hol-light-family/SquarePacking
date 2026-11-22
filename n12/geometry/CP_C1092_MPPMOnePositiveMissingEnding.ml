(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMOnePositiveMissingEnding.lean         *)
(* (N12Compact.C1092MPPMOnePositive).  Complete raw Lemma 2 of ONE-POSITIVE- *)
(* CONTINUOUS-ENDING: the eight oriented actual normals reduce to three;    *)
(* clearance, the positive longitudinal scalar and the transverse faces     *)
(* exclude them all.  Squares C, E, B are c s u v a, cE sE uE vE aE,        *)
(* cB sB uB vB aB (OpenSquare invariants explicit); PositiveMissingInput is *)
(* c1092opc_input; upper / lower / strict_bounds / ownU / ownV are ABT_*;   *)
(* SteepPositiveThreeSquare.signed_axes C1092SPTS_SIGNED_AXES; lower_pn     *)
(* C1092WS_LOWER_PN; TwoFifths.Support.lower_neg / upper_pos_neg            *)
(* C1092TFSU_*; positiveP / positiveQ / positive_longitudinal C1092OPS_*;   *)
(* positive_missing_upward C1092OPC_*.  The lets k, ell are written out.    *)
(* Tag C1092OPME_.                                                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_MPPMOnePositiveClearance.ml";;

let C1092OPME_LP_TAC = REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

let C1092OPME_PROD tm = SUBGOAL_THEN tm ASSUME_TAC THENL
  [REPEAT((MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN CONJ_TAC) THEN
   FIRST [C1092OPME_LP_TAC; REAL_ARITH_TAC]; ALL_TAC];;

(* Lean: cone (local have of positive_missing_axes) *)
let C1092OPME_CONE = prove
 (`forall c s u v a cE sE uE vE aE nx ny.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     nx pow 2 + ny pow 2 = &1 /\
     linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
     linside c s u v a (--(&13 / &50)) (&0) /\
     linside cE sE uE vE aE (&7 / &20) (--(&7 / &20)) /\
     linside cE sE uE vE aE (&0) (--(&1 / &2)) /\
     ABT_upper c s u v a nx ny <= ABT_lower cE sE uE vE aE nx ny
     ==> &0 < nx /\ &0 < (&13 / &50) * nx - ny / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (sq, (x, y)) ->
    MP_TAC(SPECL (sq @ [x; y; `nx:real`; `ny:real`]) ABT_STRICT_BOUNDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC)
   [[`c:real`; `s:real`; `u:real`; `v:real`; `a:real`], (`--(&7 / &20)`, `--(&7 / &20)`);
    [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`], (`--(&13 / &50)`, `&0`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`], (`&7 / &20`, `--(&7 / &20)`);
    [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`], (`&0`, `--(&1 / &2)`)] THEN
  C1092OPME_LP_TAC);;

let C1092OPME_UNPACK_TAC =
  REWRITE_TAC[c1092opc_input; IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `a:real = aE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092anc_core] o
    check (fun th -> can (term_match [] `c1092anc_core c s u v a`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal c (--s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal c (--s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS o
    check (fun th -> concl th = `c977cc_normal cE sE`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> concl th = `c977cc_normal cE sE`));;

(* a separating axis upper C n <= lower E n contradicting the cone *)
let C1092OPME_CONE_TAC =
  FIRST_ASSUM(fun th ->
    let tm = concl th in
    if is_binary "real_le" tm &&
       (try fst(dest_const(fst(strip_comb(lhand tm)))) = "ABT_upper" with Failure _ -> false)
    then
      let args = snd(strip_comb(lhand tm)) in
      let nx = el 5 args and ny = el 6 args in
      MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                    `cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`; nx; ny]
                   C1092OPME_CONE) THEN
      ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN
       MAP_EVERY (fun t -> MP_TAC(ASSUME t))
         [`c * c + s * s = &1`; `cE * cE + sE * sE = &1`] THEN REAL_ARITH_TAC;
       STRIP_TAC THEN C1092OPME_LP_TAC]
    else NO_TAC);;

(* Lean: positive_missing_axes (private) *)
let C1092OPME_POSITIVE_MISSING_AXES = prove
 (`forall c s u v a cE sE uE vE aE cB sB uB vB aB.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092opc_input c s u v a cE sE uE vE aE cB sB uB vB aB
     ==> u + a <= ABT_lower cE sE uE vE aE c s \/
         ABT_upper c s u v a cE sE <= uE \/
         ABT_upper c s u v a sE (--cE) <= --(vE + aE)`,
  REPEAT GEN_TAC THEN C1092OPME_UNPACK_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`] ABT_OWNU) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`] ABT_OWNV) THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`; `--sE`; `cE:real`]
    C1092TFSU_LOWER_NEG) THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG] THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`] C1092SPTS_SIGNED_AXES) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN C1092OPME_CONE_TAC);;

(* Lean: positive_missing_impossible *)
let C1092OPME_POSITIVE_MISSING_IMPOSSIBLE = prove
 (`forall c s u v a cE sE uE vE aE cB sB uB vB aB.
     c * c + s * s = &1 /\ &0 < a /\ cE * cE + sE * sE = &1 /\ &0 < aE /\
     cB * cB + sB * sB = &1 /\ &0 < aB /\
     c1092opc_input c s u v a cE sE uE vE aE cB sB uB vB aB
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL C1092OPME_POSITIVE_MISSING_AXES) THEN
  MP_TAC(SPEC_ALL C1092OPC_POSITIVE_MISSING_UPWARD) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th ->
    can (term_match [] `c1092opc_input c s u v a cE sE uE vE aE cB sB uB vB aB`) (concl th))) THEN
  C1092OPME_UNPACK_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] C1092ANC_FACES) THEN
  ASM_REWRITE_TAC[c1092anc_faces] THEN STRIP_TAC THEN
  SUBGOAL_THEN `--s < &1 / &4` ASSUME_TAC THENL [C1092OPME_LP_TAC; ALL_TAC] THEN
  (* k = c * cE + s * sE, ell = c * sE - s * cE *)
  C1092OPME_PROD `&0 <= --s * (cE - sE)` THEN
  C1092OPME_PROD `&0 <= (cE - &7 / &10) * (c + s)` THEN
  SUBGOAL_THEN `&1 / &2 < c * cE + s * sE` ASSUME_TAC THENL [C1092OPME_LP_TAC; ALL_TAC] THEN
  C1092OPME_PROD `&0 < --s * cE` THEN C1092OPME_PROD `&0 <= c * sE` THEN
  SUBGOAL_THEN `&0 < c * sE - s * cE` ASSUME_TAC THENL [C1092OPME_LP_TAC; ALL_TAC] THEN
  C1092OPME_PROD `&0 < (a - &1) * (&1 + (c * cE + s * sE) + (c * sE - s * cE))` THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC ASSUME_TAC) o
    check (is_disj o concl)) THENL
  [(* current *)
   MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `a:real`; `c:real`; `s:real`;
                 `c * cE + s * sE`; `--(c * sE - s * cE)`] C1092WS_LOWER_PN) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   C1092OPME_PROD `&0 <= (c * cE + s * sE) * ((cE - (&14 / &25) * sE) - (uE + a))` THEN
   C1092OPME_PROD `&0 <= (c * sE - s * cE) * (vE - (--cE - sE))` THEN
   MP_TAC(SPECL [`c:real`; `--s`; `cE:real`; `sE:real`] C1092OPS_POSITIVE_LONGITUDINAL) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   SUBGOAL_THEN
    `&1 - c + (c * cE + s * sE) * (&1 - cE + (&14 / &25) * sE) +
     (c * sE - s * cE) * (&1 - cE - sE) =
     &1 - c1092ops_positiveP cE sE * c - c1092ops_positiveQ cE sE * --s` ASSUME_TAC THENL
   [REWRITE_TAC[c1092ops_positiveP; c1092ops_positiveQ] THEN
    UNDISCH_TAC `cE pow 2 + sE pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   C1092OPME_LP_TAC;
   (* upward *)
   UNDISCH_TAC `linside cE sE uE vE a (&0) (--(&1 / &2))` THEN
   REWRITE_TAC[linside] THEN STRIP_TAC THEN C1092OPME_LP_TAC;
   (* downward *)
   MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `sE:real`; `--cE`;
                 `c * sE - s * cE`; `--(c * cE + s * sE)`] C1092TFSU_UPPER_POS_NEG) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
   C1092OPME_PROD `&0 <= (c * sE - s * cE) * (u + c)` THEN
   C1092OPME_PROD `&0 <= (c * cE + s * sE) * (&43 / &500 - v - a)` THEN
   C1092OPME_PROD `&0 <= (c * sE - s * cE) * (&1 - c)` THEN
   SUBGOAL_THEN `&0 < &1 - cE - sE + (c * sE - s * cE) * (&1 - c) +
                      (c * cE + s * sE) * (&1 - &43 / &500)` ASSUME_TAC THENL
   [C1092OPME_LP_TAC; ALL_TAC] THEN
   C1092OPME_LP_TAC]);;

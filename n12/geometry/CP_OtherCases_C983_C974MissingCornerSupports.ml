(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/C974MissingCornerSupports.lean *)
(* (N12Compact.Completion.OtherCases.C983.C974MissingCorner).  The complete *)
(* actual-axis reduction shared by WALL-SIGN Theorem 2 and MIDPOINT §1.4.    *)
(* Conventions of CP_OtherCases_C983_C974MissingCornerData.ml: Input K W is  *)
(* c974mc_input over the 5-tuples K = (cK,sK,uK,vK,aK), W = (cW,..,aW), the  *)
(* OpenSquare invariants (unit normal, 0 < side) are explicit hypotheses.    *)
(* upper / lower = ABT_upper / ABT_lower, strict_bounds ABT_STRICT_BOUNDS,   *)
(* SupportForms.upper_in_bands / lower_in_bands C981SF_UPPER_IN_BANDS /      *)
(* C981SF_LOWER_IN_BANDS, WallProfile.upper_neg / lower_neg OCWPVG_UPPER_NEG *)
(* / OCWPVG_LOWER_NEG; faceSeparation_of_disjoint + separated + parallel /   *)
(* transverse_radius are packaged in ABT_FOUR_AXES.  singleton_wall /        *)
(* wall_positive_caps C974MC_SINGLETON_WALL / C974MC_WALL_POSITIVE_CAPS.     *)
(* (Lean header: "no compiler replay has been performed".)  Tag C974MCS_.    *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C983_C974MissingCornerData.ml";;
needs "n12/geometry/CP_C981_SupportForms.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_VertexGeometry.ml";;
needs "n12/geometry/ABTransverse.ml";;

let C974MCS_K = "cK sK uK vK aK" and C974MCS_W = "cW sW uW vW aW";;
let C974MCS_INV =
  "cK * cK + sK * sK = &1 /\\ &0 < aK /\\ cW * cW + sW * sW = &1 /\\ &0 < aW /\\ " ^
  "c974mc_input cK sK uK vK aK cW sW uW vW aW";;
let c974mcs_tm fmt = parse_term fmt;;

(* open the input (all fields as assumptions) *)
let C974MCS_OPEN_TAC =
  FIRST_ASSUM(fun th -> if is_comb (concl th) && fst (strip_comb (concl th)) = `c974mc_input`
    then STRIP_ASSUME_TAC (REWRITE_RULE[c974mc_input] th) else NO_TAC);;

let C974MCS_SB sq x y nx ny =
  let args = map (fun s -> mk_var(s, `:real`)) (String.split_on_char ' ' sq) in
  SPECL (args @ [x; y; nx; ny]) ABT_STRICT_BOUNDS;;

(* Lean: separator_cone *)
let C974MCS_SEPARATOR_CONE = prove
 (c974mcs_tm (Printf.sprintf "!%s %s nx ny. %s /\\ nx pow 2 + ny pow 2 = &1 /\\
     ABT_upper %s nx ny <= ABT_lower %s nx ny
     ==> &0 < nx /\\ &0 < nx + &6 * ny /\\ &0 < &90 * nx - &43 * ny"
     C974MCS_K C974MCS_W C974MCS_INV C974MCS_K C974MCS_W),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C974MCS_OPEN_TAC THEN
  UNDISCH_TAC (c974mcs_tm (Printf.sprintf "ABT_upper %s nx ny <= ABT_lower %s nx ny" C974MCS_K C974MCS_W)) THEN
  MP_TAC(C974MCS_SB C974MCS_K `&41 / &50` `&0` `nx:real` `ny:real`) THEN
  MP_TAC(C974MCS_SB C974MCS_K `&24 / &25` `--(&6 / &25)` `nx:real` `ny:real`) THEN
  MP_TAC(C974MCS_SB C974MCS_W `&1` `&0` `nx:real` `ny:real`) THEN
  MP_TAC(C974MCS_SB C974MCS_W `&1` `--(&43 / &500)` `nx:real` `ny:real`) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* Lean: upper_self *)
let C974MCS_UPPER_SELF = prove
 (`forall c s u v a:real. c * c + s * s = &1 ==> ABT_upper c s u v a c s = u + a`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[C981SF_UPPER_IN_BANDS; REAL_ARITH `--c * s + s * c = &0`] THEN
  REWRITE_TAC[REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

(* Lean: lower_self *)
let C974MCS_LOWER_SELF = prove
 (`forall c s u v a:real. c * c + s * s = &1 ==> ABT_lower c s u v a c s = u`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[C981SF_LOWER_IN_BANDS; REAL_ARITH `--c * s + s * c = &0`] THEN
  REWRITE_TAC[REAL_ABS_NUM] THEN REAL_ARITH_TAC);;

(* Lean: no_reverse_v *)
let C974MCS_NO_REVERSE_V = prove
 (c974mcs_tm (Printf.sprintf "!%s %s. %s /\\ vK + aK <= &0 /\\
     ABT_upper %s sK (--cK) <= ABT_lower %s sK (--cK) ==> F"
     C974MCS_K C974MCS_W C974MCS_INV C974MCS_K C974MCS_W),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C974MCS_OPEN_TAC THEN
  SUBGOAL_THEN `ABT_upper cK sK uK vK aK sK (--cK) = --vK` ASSUME_TAC THENL
   [REWRITE_TAC[C981SF_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `sK * cK + --cK * sK = &0 /\ --sK * sK + --cK * cK = --(&1)`
      (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `cK * cK + sK * sK = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_ABS_NEG] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sK pow 2 + (--cK) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `cK * cK + sK * sK = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `sK <= &1` ASSUME_TAC THENL
   [NLIN_TAC [SQ_NONNEG `cK:real`]; ALL_TAC] THEN
  MP_TAC(C974MCS_SB C974MCS_W `&1` `&0` `sK:real` `--cK`) THEN ASM_REWRITE_TAC[] THEN
  RASM_ARITH_TAC);;

(* reverse a separation: upper W n <= lower K n  gives  upper K (-n) <= lower W (-n) *)
let C974MCS_REVERSE = prove
 (`forall cK sK uK vK aK cW sW uW vW aW nx ny:real.
     ABT_upper cW sW uW vW aW nx ny <= ABT_lower cK sK uK vK aK nx ny
     ==> ABT_upper cK sK uK vK aK (--nx) (--ny) <= ABT_lower cW sW uW vW aW (--nx) (--ny)`,
  REWRITE_TAC[OCWPVG_UPPER_NEG; OCWPVG_LOWER_NEG] THEN REAL_ARITH_TAC);;

(* Lean: separating_u *)
let C974MCS_SEPARATING_U = prove
 (c974mcs_tm (Printf.sprintf "!%s %s. %s /\\ &0 < cK /\\ &0 < sK /\\ &0 < cW /\\ vK + aK <= &0 /\\
     (ABT_upper %s (--sW) cW <= ABT_lower %s (--sW) cW ==> F) /\\
     (ABT_upper %s sW (--cW) <= ABT_lower %s sW (--cW) ==> F)
     ==> ABT_upper %s cK sK <= ABT_lower %s cK sK \\/
         ABT_upper %s cW sW <= ABT_lower %s cW sW"
     C974MCS_K C974MCS_W C974MCS_INV C974MCS_K C974MCS_W C974MCS_K C974MCS_W
     C974MCS_K C974MCS_W C974MCS_K C974MCS_W),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN (c974mcs_tm (Printf.sprintf "!nx ny. nx pow 2 + ny pow 2 = &1 /\\ &0 <= nx /\\
      ABT_upper %s nx ny <= ABT_lower %s nx ny ==> F" C974MCS_W C974MCS_K)) ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP C974MCS_REVERSE) THEN DISCH_TAC THEN
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `--nx`; `--ny`]
      C974MCS_SEPARATOR_CONE) THEN
    ASM_REWRITE_TAC[REAL_POW_NEG; ARITH] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] ABT_FOUR_AXES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `c974mc_input cK sK uK vK aK cW sW uW vW aW` THEN
    REWRITE_TAC[c974mc_input] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  let imp_tac = FIRST_ASSUM(fun th -> if is_imp (concl th) && rand (concl th) = `false` then
      (MATCH_MP_TAC (TAUT `false ==> p`) THEN MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC) else NO_TAC) in
  let norev_tac nx ny =
    MATCH_MP_TAC (TAUT `false ==> p`) THEN FIRST_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    MAP_EVERY EXISTS_TAC [nx; ny] THEN REWRITE_TAC[REAL_POW_2] THEN ASM_REWRITE_TAC[] THEN
    RASM_ARITH_TAC in
  let cone_tac =
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `--sK`; `cK:real`]
      C974MCS_SEPARATOR_CONE) THEN
    ASM_REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_2] THEN
    ANTS_TAC THENL [UNDISCH_TAC `cK * cK + sK * sK = &1` THEN REAL_ARITH_TAC; RASM_ARITH_TAC] in
  let nrv_tac =
    MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                  `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C974MCS_NO_REVERSE_V) THEN
    ASM_REWRITE_TAC[] THEN NO_TAC in
  let rev_tac = FIRST_X_ASSUM(fun th -> MP_TAC (MATCH_MP C974MCS_REVERSE th)) THEN
    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC in
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  FIRST [ASM_REWRITE_TAC[] THEN NO_TAC; imp_tac; norev_tac `cK:real` `sK:real`;
         norev_tac `cW:real` `sW:real`; cone_tac;
         rev_tac THEN FIRST [imp_tac; nrv_tac]]);;

(* replace every occurrence of the two-letter key in a string *)
let c974mcs_repl key by str =
  let b = Buffer.create 256 and n = String.length str in
  let rec go i = if i >= n then () else
    if i + 1 < n && String.sub str i 2 = key then (Buffer.add_string b by; go (i + 2))
    else (Buffer.add_char b str.[i]; go (i + 1)) in
  go 0; Buffer.contents b;;

(* Lean: positive_support_obstruction *)
let C974MCS_POSITIVE_SUPPORT_OBSTRUCTION = prove
 (c974mcs_tm (Printf.sprintf "!%s %s. %s /\\ &0 < cK /\\ &0 < sK /\\ &0 < cW /\\ &0 <= sW /\\
     sW <= cW /\\ vK + aK <= &0 /\\ &0 <= sK * cW - cK * sW
     ==> let x = sK / (&1 + cK) in
         &1 - cW + (&1 - sK) * (cW * x - sW) < &0 \\/
         (cK * cW + sK * sW) * (&1 - cW) + (sK * cW - cK * sW) * (&1 - cW / &2) - x * (&1 - sK) < &0"
     C974MCS_K C974MCS_W C974MCS_INV),
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV let_CONV) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C974MCS_SEPARATING_U) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `sW * sW + cW * cW = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `cW * cW + sW * sW = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `--sW`; `cW:real`]
        C974MCS_SEPARATOR_CONE);
      MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                    `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`; `sW:real`; `--cW`]
        C974MCS_SEPARATOR_CONE)] THEN
    ASM_REWRITE_TAC[REAL_POW_NEG; ARITH; REAL_POW_2] THEN RASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C974MC_SINGLETON_WALL) THEN
  MP_TAC(SPECL [`cK:real`; `sK:real`; `uK:real`; `vK:real`; `aK:real`;
                `cW:real`; `sW:real`; `uW:real`; `vW:real`; `aW:real`] C974MC_WALL_POSITIVE_CAPS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `&1 < aK /\ aK = aW` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `c974mc_input cK sK uK vK aK cW sW uW vW aW` THEN
    SIMP_TAC[c974mc_input]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `aK:real = aW`)) THEN
  SUBGOAL_THEN `sK / (&1 + cK) * (&1 + cK) = sK` MP_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN UNDISCH_TAC `&0 < cK` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SPEC_TAC(`sK / (&1 + cK)`, `x:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `sK * x = &1 - cK` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_EQ_RCANCEL_IMP THEN EXISTS_TAC `&1 + cK` THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 < cK` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`x * (&1 + cK) = sK`; `cK * cK + sK * sK = &1`] THEN
    CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < cK * cW + sK * sW` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LTE_ADD THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [(* along K *)
    DISJ2_TAC THEN
    UNDISCH_TAC `ABT_upper cK sK uK vK aK cK sK <= ABT_lower cW sW uW vW aK cK sK` THEN
    ASM_SIMP_TAC[C974MCS_UPPER_SELF; C981SF_LOWER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cK * cW + sK * sW) = cK * cW + sK * sW /\
                  abs(--cK * sW + sK * cW) = sK * cW - cK * sW` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < sK * (uK + aK - (&1 - x))` ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 <= cK * --(vK + aK) /\ &0 < (aK - &1) * (cK + sK)` MP_TAC THENL
       [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
        ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC [`aK * cK - &1 <= sK * uK + cK * (vK + aK)`; `sK * x = &1 - cK`] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&1 - x < uK + aK` ASSUME_TAC THENL
     [MP_TAC(SPECL [`sK:real`; `uK + aK - (&1 - x)`] (CONJUNCT1 REAL_LT_MUL_EQ)) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= (cK * cW + sK * sW) * (cW - (uW - cW + aK)) /\
                  &0 <= (sK * cW - cK * sW) * (cW / &2 - (vW + sW + aK)) /\
                  &0 < (aK - &1) * ((cK * cW + sK * sW) + (sK * cW - cK * sW))` MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LE_MUL; MATCH_MP_TAC REAL_LT_MUL] THEN
      ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `cK * (cW * cW + sW * sW) = cK` MP_TAC THENL
     [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`uK + aK <= (cK * cW + sK * sW) * (uW + aK / &2) + (--cK * sW + sK * cW) * (vW + aK / &2) -
                  aK / &2 * ((cK * cW + sK * sW) + (sK * cW - cK * sW))`;
      `&1 - x < uK + aK`; `sK * x = &1 - cK`] THEN
    REAL_ARITH_TAC;
    (* along W *)
    DISJ1_TAC THEN
    UNDISCH_TAC `ABT_upper cK sK uK vK aK cW sW <= ABT_lower cW sW uW vW aK cW sW` THEN
    ASM_SIMP_TAC[C974MCS_LOWER_SELF; C981SF_UPPER_IN_BANDS] THEN
    SUBGOAL_THEN `abs(cW * cK + sW * sK) = cK * cW + sK * sW /\
                  abs(--cW * sK + sW * cK) = sK * cW - cK * sW` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
    let k = "(cK * cW + sK * sW)" and sv = "(sK * cW - cK * sW)" in
    let tm f = parse_term (c974mcs_repl "SS" sv (c974mcs_repl "KK" k f)) in
    SUBGOAL_THEN (tm "KK * uK + aK * (KK + SS) - SS * (vK + aK) <= &2 * cW - aK") ASSUME_TAC THENL
     [MAP_EVERY (fun th -> FIRST_X_ASSUM(MP_TAC o check (fun t -> concl t = th)))
       [tm "(cW * cK + sW * sK) * (uK + aK / &2) + (--cW * sK + sW * cK) * (vK + aK / &2) + aK / &2 * (KK + SS) <= uW";
        `uW + aK <= &2 * cW`] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (tm "sK * (KK * (&1 - x) + SS + &1 - &2 * cW) < &0") ASSUME_TAC THENL
     [SUBGOAL_THEN (tm "&0 <= KK * ((sK * uK + cK * (vK + aK)) - (aK * cK - &1)) /\\
                    &0 <= (sK * SS + KK * cK) * --(vK + aK) /\\
                    &0 <= sK * ((&2 * cW - aK) - (KK * uK + aK * (KK + SS) - SS * (vK + aK))) /\\
                    &0 < (aK - &1) * (sK * (KK + SS) + KK * cK + sK) /\\
                    KK * (sK * x - (&1 - cK)) = &0") MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
            ASM_REAL_ARITH_TAC;
            ASM_REAL_ARITH_TAC];
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
           [ASM_REAL_ARITH_TAC;
            SUBGOAL_THEN (tm "&0 <= sK * (KK + SS) /\\ &0 <= KK * cK") MP_TAC THENL
             [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
            UNDISCH_TAC `&0 < sK` THEN REAL_ARITH_TAC];
          ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO]];
        ALL_TAC] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (tm "KK * (&1 - x) + SS + &1 - &2 * cW < &0") ASSUME_TAC THENL
     [MP_TAC(SPECL [`sK:real`; tm "--(KK * (&1 - x) + SS + &1 - &2 * cW)"] (CONJUNCT1 REAL_LT_MUL_EQ)) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o check (fun t -> concl t = tm "sK * (KK * (&1 - x) + SS + &1 - &2 * cW) < &0")) THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN (tm "KK * (&1 - x) + SS - cW = (&1 - sK) * (cW * x - sW)") ASSUME_TAC THENL
     [SUBGOAL_THEN `(cW - sW) * (sK * x) = (cW - sW) * (&1 - cK) /\
                    cW * (x * (&1 + cK)) = cW * sK` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY (fun th -> FIRST_X_ASSUM(MP_TAC o check (fun t -> concl t = th)))
      [tm "KK * (&1 - x) + SS + &1 - &2 * cW < &0"; tm "KK * (&1 - x) + SS - cW = (&1 - sK) * (cW * x - sW)"] THEN
    REAL_ARITH_TAC]);;

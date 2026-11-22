(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C983/NegativeMixedSouth.lean        *)
(* (N12Compact.Completion.OtherCases.C983.NegativeMixedSouth).  The         *)
(* southeast-owned transverse / right-owned parallel separation.  Squares   *)
(* E, N, R are cE sE uE vE aE, cN sN uN vN aN, cR sR uR vR aR (unit normals *)
(* and positive sides explicit).  Vocabulary as in NegativeRightOwned.ml:   *)
(* RightTripleData.Input = ocrtd_input, NegativeTripleFaces.Data =           *)
(* ccntf_data, upper / lower / ownU / ownV = ABT_upper / ABT_lower /         *)
(* ABT_OWNU / ABT_OWNV.  Lean c, t, a, b are cE, --sE, cR, --sR, and the     *)
(* Lean `let` abbreviations P = a*t-b*c, Q = a*c+b*t, H = vE+aE,             *)
(* V = uE+aE are written out.  The Lean vertex bounds                        *)
(* (WallProfile.vertex + closed_bounds) are replaced by the band form of     *)
(* the lower support (C983NMSO_LOWER_LE).  Tag C983NMSO_.                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeMixedScalars.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeMixedShallow.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeRightOwned.ml";;
needs "n12/geometry/CP_OtherCases_C983_NegativeCentralOrder.ml";;

let C983NMSO_LIN = C983NRO_LIN;;
let C983NMSO_PROD = C983NRO_PROD;;
let C983NMSO_FACT = C983NRO_FACT;;
let C983NMSO_RING = C983NRO_RING;;
let C983NMSO_MP th = MP_TAC th THEN ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC];;

(* term builder: the Lean abbreviations P, Q, H, V inside a quotation string *)
let c983nmso_tm s =
  let rec rep a b s =
    let la = String.length a and ls = String.length s in
    let rec find i = if i + la > ls then -1
      else if String.sub s i la = a then i else find (i + 1) in
    let i = find 0 in
    if i < 0 then s
    else String.sub s 0 i ^ b ^ rep a b (String.sub s (i + la) (ls - i - la)) in
  parse_term
   (rep "PP" "(cR * --sE - --sR * cE)"
   (rep "QQ" "(cR * cE + --sR * --sE)"
   (rep "HH" "(vE + aE)"
   (rep "VV" "(uE + aE)" s))));;

let C983NMSO_SQ = [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`;
                   `cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                   `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`];;

(* helper: the lower support is below both left vertices' band values *)
let C983NMSO_LOWER_LE = prove
 (`forall c s u v a nx ny. &0 < a
     ==> ABT_lower c s u v a nx ny <= (nx * c + ny * s) * u + (--nx * s + ny * c) * v /\
         ABT_lower c s u v a nx ny <= (nx * c + ny * s) * (u + a) + (--nx * s + ny * c) * v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[C981SF_LOWER_IN_BANDS] THEN
  REWRITE_TAC[real_abs] THEN
  REPEAT COND_CASES_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  CONJ_TAC THEN NLIN_TAC []);;

(* Lean: height_floor (private) *)
let C983NMSO_HEIGHT_FLOOR = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t
     ==> (&4 / &5) * t < v + a`,
  C983NRO_E_TAC THEN
  C983NMSO_RING `c pow 2 + t pow 2 = &1` THEN
  MP_TAC(SPECL [`c:real`; `t:real`] CCCS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NMSO_LIN; STRIP_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [C983NMSO_LIN; ALL_TAC] THEN
  C983NMSO_PROD `&0 < c * (a - &1)` THEN
  C983NMSO_PROD `&0 < t * ((u + a) - &1)` THEN
  SUBGOAL_THEN `&0 < c * ((v + a) - (&4 / &5) * t)` ASSUME_TAC THENL
   [C983NMSO_LIN; ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC C983NRO_POS_CANCEL THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]);;

(* Lean: second_floor (private) *)
let C983NMSO_SECOND_FLOOR = prove
 (`forall c s u v a t.
     c * c + s * s = &1 /\ &0 < a /\ ccntf_data c s u v a t /\ &9 / &41 <= t
     ==> &1 - (&1 - t) / c < v + a`,
  C983NRO_E_TAC THEN
  C983NMSO_RING `c pow 2 + t pow 2 = &1` THEN
  ABBREV_TAC `e = (&1 - t) / c` THEN
  SUBGOAL_THEN `c * e = &1 - t` ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN MATCH_MP_TAC REAL_DIV_LMUL THEN C983NMSO_LIN; ALL_TAC] THEN
  C983NMSO_PROD `&0 < c * (a - &1)` THEN
  SUBGOAL_THEN `&0 < c * ((v + a) - (&1 - e))` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
     [MP_TAC(SPECL [`c:real`; `t:real`] C983NRO_THRESHOLD_PHASE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NMSO_LIN; DISCH_TAC] THEN
      C983NMSO_PROD `&0 <= t * ((t + (&4 / &5) * c) - &1)` THEN
      C983NMSO_PROD `&0 <= c * (v - ((&4 / &5) * t - c))` THEN
      C983NMSO_LIN;
      C983NMSO_PROD `&0 < t * ((u + a) - &1)` THEN C983NMSO_LIN];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN MATCH_MP_TAC C983NRO_POS_CANCEL THEN
  EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[]);;

(* Lean: wall (private) *)
let C983NMSO_WALL = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR U.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR /\
     ABT_upper cE sE uE vE aE (--sE) cE <= ABT_lower cR sR uR vR aR (--sE) cE /\
     U < ABT_upper cN sN uN vN aN cR sR /\
     &0 <= cE * U + --sR * (vE + aE) - (cR * cE + --sR * --sE) * (&2 - cR - --sR)
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C983NRO_INPUT_TAC THEN
  C983NMSO_MP(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNU) THEN
  C983NMSO_MP(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
  C983NMSO_MP(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `--sE`; `cE:real`]
    C983NMSO_LOWER_LE) THEN
  C983NMSO_PROD `&0 < cR * cE` THEN C983NMSO_PROD `&0 <= --sR * --sE` THEN
  C983NMSO_FACT (c983nmso_tm "&0 < QQ") THEN
  C983NMSO_PROD (c983nmso_tm "&0 <= --sR * ((PP * uR + QQ * vR) - HH)") THEN
  C983NMSO_PROD (c983nmso_tm "&0 <= QQ * (&2 - (cR * (uR + aR) - sR * (vR + aR)))") THEN
  C983NMSO_PROD `&0 < cE * (uR - U)` THEN
  C983NMSO_PROD (c983nmso_tm "&0 < QQ * (cR + --sR)") THEN
  C983NMSO_PROD (c983nmso_tm "&0 < (QQ * (cR + --sR)) * (aR - &1)") THEN
  C983NMSO_RING (c983nmso_tm "uR * (--sR * PP - cR * QQ) = uR * --cE") THEN
  C983NMSO_LIN);;

(* Lean: steeper (private) *)
let C983NMSO_STEEPER = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR /\
     ABT_upper cE sE uE vE aE (--sE) cE <= ABT_lower cR sR uR vR aR (--sE) cE /\
     cR * --sE - --sR * cE <= &0
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `ABT_upper cE sE uE vE aE (--sR) cR <= ABT_lower cR sR uR vR aR (--sR) cR`
    ASSUME_TAC THENL
   [C983NRO_INPUT_TAC THEN
    C983NMSO_MP(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNU) THEN
    C983NMSO_MP(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] ABT_OWNV) THEN
    C983NMSO_MP(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`] ABT_OWNV) THEN
    C983NMSO_PROD `&0 < cR * cE` THEN C983NMSO_PROD `&0 <= --sR * --sE` THEN
    C983NMSO_FACT (c983nmso_tm "&0 < QQ") THEN
    C983NMSO_RING `cE pow 2 + (--sE) pow 2 = &1` THEN
    C983NMSO_RING (c983nmso_tm "QQ pow 2 + PP pow 2 = &1") THEN
    MP_TAC(SPECL [c983nmso_tm "QQ"; c983nmso_tm "PP"] C983NRO_UNIT_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `--sE`] C983NRO_UNIT_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] OCNTNS_RIGHT_AXIS_BOUNDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ocrtd_rightprofile]; STRIP_TAC] THEN
    MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cR:real`; `--sR`]
      C983NRO_NORTH_FLOOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NMSO_LIN;
                    REWRITE_TAC[REAL_NEG_NEG] THEN DISCH_TAC] THEN
    C983NMSO_FACT `&1 - --sR < uR` THEN
    (* dotBound *)
    C983NMSO_RING (c983nmso_tm
      "(--sR * cE - (&1 + cR) * --sE) pow 2 = (&1 + cR) * (&1 + cR - &2 * cE * QQ)") THEN
    SUBGOAL_THEN (c983nmso_tm "&2 * cE * QQ <= &1 + cR") ASSUME_TAC THENL
     [SUBGOAL_THEN (c983nmso_tm "&0 <= &1 + cR - &2 * cE * QQ") MP_TAC THENL
       [MATCH_MP_TAC C983NRO_NN_CANCEL THEN EXISTS_TAC `&1 + cR` THEN CONJ_TAC THENL
         [C983NMSO_LIN;
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = c983nmso_tm
            "(--sR * cE - (&1 + cR) * --sE) pow 2 = (&1 + cR) * (&1 + cR - &2 * cE * QQ)")) THEN
          REWRITE_TAC[REAL_LE_POW_2]];
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    (* small *)
    SUBGOAL_THEN (c983nmso_tm "(&13 / &50) * cE * QQ < uR") ASSUME_TAC THENL
     [ASM_CASES_TAC `--sR <= &2 / &3` THENL
       [C983NMSO_PROD (c983nmso_tm "&0 <= cE * (&1 - QQ)") THEN C983NMSO_LIN;
        RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
        SUBGOAL_THEN `cR < &3 / &4` ASSUME_TAC THENL
         [C983NMSO_PROD `&0 < (--sR - &2 / &3) * (--sR + &2 / &3)` THEN
          REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
          C983NMSO_PROD `&0 <= (cR - &3 / &4) * (cR + &3 / &4)` THEN C983NMSO_LIN;
          C983NMSO_LIN]];
      ALL_TAC] THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`]
      C983NMSO_HEIGHT_FLOOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    C983NMSO_PROD (c983nmso_tm "&0 < QQ * ((&13 / &50) * cE - uE)") THEN
    C983NMSO_PROD (c983nmso_tm "&0 <= (&1 - QQ) * aE") THEN
    C983NMSO_PROD (c983nmso_tm "&0 <= --PP * HH") THEN
    C983NMSO_FACT (c983nmso_tm "QQ * VV + PP * HH < uR + aR") THEN
    C983NMSO_MP(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`; `--sE`; `cE:real`]
      C983NMSO_LOWER_LE) THEN
    C983NMSO_FACT (c983nmso_tm "HH <= PP * (uR + aR) + QQ * vR") THEN
    C983NMSO_PROD (c983nmso_tm "&0 <= --PP * ((uR + aR) - (QQ * VV + PP * HH))") THEN
    MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sR`; `cR:real`]
      C983NRO_UPPER_PP) THEN
    ANTS_TAC THENL [CONJ_TAC THEN C983NMSO_LIN; DISCH_TAC] THEN
    C983NMSO_RING (c983nmso_tm
      "HH - PP * (QQ * VV + PP * HH) - QQ * vR = QQ * ((--PP * VV + QQ * HH) - vR)") THEN
    C983NMSO_FACT (c983nmso_tm "QQ * ((--PP * VV + QQ * HH) - vR) <= &0") THEN
    SUBGOAL_THEN (c983nmso_tm "--PP * VV + QQ * HH <= vR") ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C983NMSO_PROD (c983nmso_tm "&0 < QQ * ((--PP * VV + QQ * HH) - vR)") THEN
      C983NMSO_LIN;
      ALL_TAC] THEN
    C983NMSO_LIN;
    ALL_TAC] THEN
  MATCH_MP_TAC(SPECL C983NMSO_SQ C983NRO_IMPOSSIBLE) THEN ASM_REWRITE_TAC[]);;

(* Lean: impossible *)
let C983NMSO_IMPOSSIBLE = prove
 (`forall cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR.
     cE * cE + sE * sE = &1 /\ &0 < aE /\ cN * cN + sN * sN = &1 /\ &0 < aN /\
     cR * cR + sR * sR = &1 /\ &0 < aR /\
     ocrtd_input cE sE uE vE aE cN sN uN vN aN cR sR uR vR aR /\
     ABT_upper cN sN uN vN aN cR sR <= ABT_lower cR sR uR vR aR cR sR /\
     ABT_upper cE sE uE vE aE (--sE) cE <= ABT_lower cR sR uR vR aR (--sE) cE
     ==> false`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `--sR <= &9 / &41` THENL
   [MATCH_MP_TAC(SPECL (C983NMSO_SQ @ [`(&26 / &25) * cR - --sR`]) C983NMSO_WALL) THEN
    ASM_REWRITE_TAC[] THEN C983NRO_INPUT_TAC THEN CONJ_TAC THENL
     [MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cR:real`; `--sR`]
        C983NRO_NORTH_SHALLOW_FLOOR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NMSO_LIN; REWRITE_TAC[REAL_NEG_NEG]];
      MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`]
        C983NMSO_HEIGHT_FLOOR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      C983NMSO_RING `cE pow 2 + (--sE) pow 2 = &1` THEN
      MP_TAC(SPECL [`cE:real`; `--sE`; `cR:real`; `--sR`; `vE + aE`] C983NMS_SCALAR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NMSO_LIN; DISCH_TAC] THEN
      C983NMSO_LIN];
    ALL_TAC] THEN
  ASM_CASES_TAC `cR * --sE - --sR * cE <= &0` THENL
   [MATCH_MP_TAC(SPECL C983NMSO_SQ C983NMSO_STEEPER) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(SPECL (C983NMSO_SQ @ [`&1 - --sR`]) C983NMSO_WALL) THEN
  ASM_REWRITE_TAC[] THEN C983NRO_INPUT_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LE]) THEN
  C983NMSO_RING `cE pow 2 + (--sE) pow 2 = &1` THEN
  (* relation *)
  SUBGOAL_THEN `--sR <= --sE` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C983NMSO_PROD `&0 < cR * --sE` THEN C983NMSO_PROD `&0 <= --sR * cE` THEN
    C983NMSO_FACT `&0 < cR * --sE + --sR * cE` THEN
    C983NMSO_PROD `&0 < (cR * --sE - --sR * cE) * (cR * --sE + --sR * cE)` THEN
    C983NMSO_PROD `&0 < (--sR - --sE) * (--sR + --sE)` THEN
    C983NMSO_RING `(cR * --sE - --sR * cE) * (cR * --sE + --sR * cE) =
                   (--sE) pow 2 - (--sR) pow 2` THEN
    C983NMSO_LIN;
    ALL_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`]
    C983NMSO_SECOND_FLOOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN C983NMSO_LIN; DISCH_TAC] THEN
  MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`;
                `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`] OCNTNS_RIGHT_AXIS_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[ocrtd_rightprofile]; STRIP_TAC] THEN
  MP_TAC(SPECL [`cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sE`]
    C983NCO_COSINE_GT_SIX_SEVENTHS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`cN:real`; `sN:real`; `uN:real`; `vN:real`; `aN:real`; `cR:real`; `--sR`]
      C983NRO_NORTH_FLOOR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NMSO_LIN;
                    REWRITE_TAC[REAL_NEG_NEG]];
    MP_TAC(SPECL [`cE:real`; `--sE`; `cR:real`; `--sR`] C983NMSC_LARGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN C983NMSO_LIN; DISCH_TAC] THEN
    C983NMSO_PROD `&0 <= --sR * ((vE + aE) - (&1 - (&1 - --sE) / cE))` THEN
    C983NMSO_LIN]);;

(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeOutwardRemainingScalars.lean      *)
(* (Jatloe, N12-jatloe; namespace N12Compact.C868.UpperNegativeOutward-     *)
(* Scalars).  The remaining longitudinal margin for the same outward pair.   *)
(* Scalar; tag C868RS_.  Private endpointCosine = 229551/270449,             *)
(* endpointSine = 143000/270449, alpha = 45645230202/73142661601,            *)
(* beta = 29192352650343/36571330800500 are inlined.                         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/CP_CommonCases_UnitCircleChord.ml";;
needs "n12/geometry/UpperNegativeOutwardScalars.ml";;

(* Lean: leftMargin (definition) *)
let c868rs_leftmargin = new_definition
 `c868rs_leftmargin (c:real) (s:real) (d:real) (t:real) =
    &1 - c - (&1043 / &500) * s + (c + s) * d + (s - c) * t -
    (&1 / &5) * t * (s * d - c * t)`;;

let C868RS_TERM s =
  let rep = ["EC", "(&229551 / &270449)"; "ES", "(&143000 / &270449)";
             "ALPHA", "(&45645230202 / &73142661601)";
             "BETA", "(&29192352650343 / &36571330800500)"] in
  let rec repl k v s =
    let n = String.length s and m = String.length k in
    let rec go i =
      if i + m > n then s
      else if String.sub s i m = k then
        String.sub s 0 i ^ v ^ repl k v (String.sub s (i + m) (n - i - m))
      else go (i + 1) in
    go 0 in
  let s = List.fold_left (fun s (k, v) -> repl k v s) s rep in
  parse_term s;;

(* Lean: endpoint_value (private) *)
let C868RS_ENDPOINT_VALUE = prove
 (C868RS_TERM "!c s. c868rs_leftmargin c s EC ES = &1 - ALPHA * c - BETA * s",
  REWRITE_TAC[c868rs_leftmargin] THEN REAL_ARITH_TAC);;

(* Lean: endpoint_comparison (private) *)
let C868RS_ENDPOINT_COMPARISON = prove
 (C868RS_TERM
   "!c s d t. c977cc_normal c s /\\ c977cc_normal d t /\\
              &1000 < &525 * c + &961 * s /\\ &1 < d + (&143 / &500) * t
              ==> c868rs_leftmargin c s EC ES <= c868rs_leftmargin c s d t",
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C868OS_STEEP_OF_PROJECTION) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`d:real`; `t:real`] C868OS_OUTWARD_SINE_CAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C868OS_NORMAL_ASSUME (ASSUME `c977cc_normal c s`) THEN
  C868OS_NORMAL_ASSUME (ASSUME `c977cc_normal d t`) THEN
  C868OS_USE CCUCC_COSINE_ORDER (map C868RS_TERM ["d:real"; "t:real"; "EC"; "ES"]) THEN
  REWRITE_TAC[c868rs_leftmargin] THEN
  SUBGOAL_THEN (C868RS_TERM "(d - EC) * (d + EC) = (ES - t) * (ES + t)")
    ASSUME_TAC THENL
  [UNDISCH_TAC `d pow 2 + t pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [] (map C868RS_TERM
   ["&0 <= (d - EC) * (&2 - d - EC)"; "&0 <= (ES - t) * t"]) THEN
  NLIN_FACTS_TAC [] (map C868RS_TERM ["ES * (ES - t) <= &2 * (d - EC)"]) THEN
  NLIN_FACTS_TAC [] (map C868RS_TERM ["&0 <= s * (&1 - t)"]) THEN
  NLIN_FACTS_TAC [] (map C868RS_TERM
   ["s * t <= &1";
    "&4 / &5 <= c + s - s * t / &5";
    "&0 <= c * (ES - t)";
    "&0 <= (&4 / &5 - c) * (&2 * ES)";
    "&0 <= s * (EC / &5)"]) THEN
  NLIN_FACTS_TAC [] (map C868RS_TERM
   ["--(&8 / &25) * ES <= c - s + s * EC / &5 - c * (t + ES) / &5"]) THEN
  NLIN_FACTS_TAC [] (map C868RS_TERM
   ["&0 <= (d - EC) * ((c + s - s * t / &5) - &4 / &5)";
    "&0 <= (ES - t) * ((c - s + s * EC / &5 - c * (t + ES) / &5) - --(&8 / &25) * ES)";
    "&0 <= (&2 / &5) * (&2 * (d - EC) - ES * (ES - t))";
    "&0 <= ((&2 / &25) * ES) * (ES - t)"]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: normal_sum_cap (private) *)
let C868RS_NORMAL_SUM_CAP = prove
 (`forall c s. c977cc_normal c s ==> c + s <= &99 / &70`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun h -> C868OS_NORMAL_ASSUME h) THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  NLIN_FACTS_TAC [] [`&0 < (c + s - &99 / &70) * (c + s + &99 / &70)`] THEN
  NLIN_TAC ~deg2:false [SQ_NONNEG `c - s:real`]);;

(* Lean: left_axis_weak *)
let C868RS_LEFT_AXIS_WEAK = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &1000 < &525 * c + &961 * s /\ &1 < d + (&143 / &500) * t
             ==> --(&3 / &500) <= c868rs_leftmargin c s d t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C868RS_ENDPOINT_COMPARISON) THEN
  REWRITE_TAC[C868RS_ENDPOINT_VALUE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP C868RS_NORMAL_SUM_CAP o CONJUNCT1) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[c977cc_normal] o CONJUNCT1) THEN
  SPEC_TAC(`c868rs_leftmargin c s d t`, `m:real`) THEN
  REPEAT STRIP_TAC THEN
  NLIN_FACTS_TAC [] (map C868RS_TERM
   ["&0 <= ((BETA - ALPHA) / &2) * (c - s)";
    "&0 <= ((ALPHA + BETA) / &2) * (&99 / &70 - (c + s))"]) THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: left_axis_margin *)
let C868RS_LEFT_AXIS_MARGIN = prove
 (`forall c s d t. c977cc_normal c s /\ c977cc_normal d t /\
             &1000 < &525 * c + &961 * s /\ &1 < d + (&143 / &500) * t /\
             &1 < (&21 / &20) * c + (&31 / &100) * s
             ==> &1 / &250 <= c868rs_leftmargin c s d t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `d:real`; `t:real`] C868RS_ENDPOINT_COMPARISON) THEN
  ASM_REWRITE_TAC[C868RS_ENDPOINT_VALUE] THEN
  SPEC_TAC(`c868rs_leftmargin c s d t`, `m:real`) THEN GEN_TAC THEN DISCH_TAC THEN
  C868OS_NORMAL_ASSUME (ASSUME `c977cc_normal c s`) THEN
  SUBGOAL_THEN `s < &48 / &73` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
   C868OS_USE CCUCC_DECREASING [`&55 / &73`; `&48 / &73`; `c:real`; `s:real`;
                                `&21 / &20`; `&31 / &100`] THEN
   NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  C868OS_USE CCUCC_INCREASING (map C868RS_TERM
    ["&55 / &73"; "&48 / &73"; "c:real"; "s:real"; "ALPHA"; "BETA"]) THEN
  NLIN_TAC ~deg2:false []);;

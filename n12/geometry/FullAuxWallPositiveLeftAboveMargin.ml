(* ========================================================================= *)
(* Port of Compact/Geometry/FullAuxWallPositiveLeftAboveMargin.lean.          *)
(* Upper relative-angle support margin.                                      *)
(* Lean variables C S of `margin` are named cc ss here.                      *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerSectorBounds.ml";;

let FAWPLAM_NEG_OF_MUL = prove
 (`forall k x. &0 < k /\ k * x < &0 ==> x < &0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= k * x` MP_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

let FAWPLAM_MUL_NONPOS = prove
 (`forall a b. &0 <= a /\ b <= &0 ==> a * b <= &0`,
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`a:real`; `--b:real`] REAL_LE_MUL) THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: diagonal (private) *)
let FAWPLAM_DIAGONAL = prove
 (`forall l r. c977cc_normal l r /\ &4 / &25 <= r /\ r <= &1 / &2
         ==> &2 - (&543 / &500) * r pow 2 - &2 * l + l / &1000 < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - l) * (l + &2)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 + l) * (&2 - (&543 / &500) * r pow 2 - &2 * l + l / &1000) =
    --(r pow 2) * ((&543 / &500) * (&1 + l) - &2) + l * (&1 + l) / &1000`
  ASSUME_TAC THENL
  [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  MATCH_MP_TAC FAWPLAM_NEG_OF_MUL THEN EXISTS_TAC `&1 + l` THEN CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  REWRITE_TAC[REAL_POW_2] THEN
  ASM_CASES_TAC `r <= &3 / &10` THENL
  [SUBGOAL_THEN `&19 / &20 <= l` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&3 / &10 - r) * (&3 / &10 + r) /\
                  &0 <= (&19 / &20 - l) * (&19 / &20 + l)` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (r * r) * ((&543 / &500) * (&1 + l) - &2 - &117 / &1000) /\
                 &0 <= (r - &4 / &25) * (r + &4 / &25)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   SUBGOAL_THEN `&433 / &500 <= l` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (&1 / &2 - r) * (&1 / &2 + r) /\
                  &0 <= (&433 / &500 - l) * (&433 / &500 + l)` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= (r * r) * ((&543 / &500) * (&1 + l) - &2 - &13 / &500) /\
                 &0 <= (r - &3 / &10) * (r + &3 / &10)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_SQUARE] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC]);;

(* Lean: cosine_line (private) *)
let FAWPLAM_COSINE_LINE = prove
 (`forall l r. c977cc_normal l r /\ &1 / &2 <= r ==> &5 / &4 - (&77 / &100) * r <= l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CSB_NORMAL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
  SUBGOAL_THEN `r <= &71 / &100` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < (r - &71 / &100) * (r + &71 / &100) /\
                 &0 <= (l - r) * (l + r)` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (r - &1 / &2) * (&71 / &100 - r)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&5 / &4 - (&77 / &100) * r) * (&5 / &4 - (&77 / &100) * r) + r * r
                <= &1` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < ((&5 / &4 - (&77 / &100) * r) - l) *
                     ((&5 / &4 - (&77 / &100) * r) + l)` MP_TAC THENL
  [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* the polynomial P of the Lean proof, with K f g p written out *)
let FAWPLAM_P x =
  let tm = `(&2 - (&999 / &1000 - ss / &2) * cc) - (&5 / &4 - (&77 / &100) * x) +
            ((&999 / &1000 - ss / &2) * cc - &543 / &500) * x pow 2 -
            (&1 / &2 + (&999 / &1000) * ss - ss pow 2 / &2) *
            (&5 / &4 - (&77 / &100) * x) * x` in
  vsubst [x,`x:real`] tm;;

let FAWPLAM_E =
  `&2 - (&543 / &500) * r pow 2 - l * (&1 + (l * cc + r * ss)) -
   (&1 / &2) * l * cc * (r * cc - l * ss) + l * (l * cc + r * ss) / &1000`;;

(* Lean: margin *)
let FAWPLAM_MARGIN = prove
 (`forall l r cc ss u.
     c977cc_normal l r /\ c977cc_normal cc ss /\
     &4 / &25 <= r /\ &1 / &20 <= ss /\ ss <= &11 / &50 /\
     &0 <= u /\ u <= &1 / &1000 /\ &0 <= r * cc - l * ss
     ==> &2 - (&543 / &500) * r pow 2 - l * (&1 + (l * cc + r * ss)) -
         (&1 / &2) * l * cc * (r * cc - l * ss) + l * (l * cc + r * ss) * u <= &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`l:real`; `r:real`; `cc:real`; `ss:real`] C977CSB_DOT_LE_ONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  C977CSB_NORMAL_TAC THEN
  SUBGOAL_THEN `&0 <= l * cc + r * ss` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (l * (l * cc + r * ss)) * (&1 / &1000 - u)` ASSUME_TAC THENL
  [REPEAT(MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC) THEN ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):real->real->bool` FAWPLAM_E `&0`) MP_TAC THENL
  [ALL_TAC; UNDISCH_TAC `&0 <= (l * (l * cc + r * ss)) * (&1 / &1000 - u)` THEN
   REAL_ARITH_TAC] THEN
  ASM_CASES_TAC `r <= &1 / &2` THENL
  [MP_TAC(SPECL [`l:real`; `r:real`] FAWPLAM_DIAGONAL) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   SUBGOAL_THEN `(l * cc + r * ss) pow 2 + (r * cc - l * ss) pow 2 = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN
    UNDISCH_TAC `cc pow 2 + ss pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   SUBGOAL_THEN `r * cc - l * ss <= cc / &2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= cc * (&1 / &2 - r) /\ &0 <= l * ss` MP_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `l * cc + r * ss <= &1` THEN
   UNDISCH_TAC `&0 <= l * cc + r * ss` THEN
   UNDISCH_TAC `&0 <= r * cc - l * ss` THEN
   UNDISCH_TAC `r * cc - l * ss <= cc / &2` THEN
   UNDISCH_TAC `(l * cc + r * ss) pow 2 + (r * cc - l * ss) pow 2 = &1` THEN
   UNDISCH_TAC `&2 - (&543 / &500) * r pow 2 - &2 * l + l / &1000 < &0` THEN
   UNDISCH_TAC `&7 / &10 <= l` THEN UNDISCH_TAC `&7 / &10 <= cc` THEN
   POP_ASSUM_LIST(K ALL_TAC) THEN
   SPEC_TAC(`l * cc + r * ss`,`al:real`) THEN SPEC_TAC(`r * cc - l * ss`,`h:real`) THEN
   REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= al * (&1 - al) /\ &0 <= h * (cc / &2 - h)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `&0 <= l * (cc * h / &2 - (&1 - al)) /\ &0 <= l * (&1 - al)`
   MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `r <= &71 / &100` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 < (r - &71 / &100) * (r + &71 / &100) /\
                 &0 <= (l - r) * (l + r)` MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&11 / &50 - ss) * (&11 / &50 + ss)` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&97 / &100 <= cc` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   SUBGOAL_THEN `&0 <= (&97 / &100 - cc) * (&97 / &100 + cc)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `cc pow 2 + ss pow 2 = &1` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - (&51 / &100) * ss pow 2 <= cc` ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&1 - cc) * ((&51 / &100) * cc - &49 / &100)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   UNDISCH_TAC `cc pow 2 + ss pow 2 = &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= &999 / &1000 - ss / &2` ASSUME_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 <= &1 / &2 + (&999 / &1000) * ss - ss pow 2 / &2`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= ss * (&999 / &1000 - ss / &2)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--(&1 / &4) <= (&999 / &1000 - ss / &2) * cc - &543 / &500`
  ASSUME_TAC THENL
  [SUBGOAL_THEN `&0 <= (&999 / &1000 - ss / &2) * (cc - &97 / &100)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`l:real`; `r:real`] FAWPLAM_COSINE_LINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `&0 <= (l - (&5 / &4 - (&77 / &100) * r)) *
          (&1 + (&1 / &2 + (&999 / &1000) * ss - ss pow 2 / &2) * r)`
  ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> &0 <= &1 + x`) THEN
   MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):real->real->bool` FAWPLAM_E (FAWPLAM_P `r:real`))
  ASSUME_TAC THENL
  [SUBGOAL_THEN
    (mk_eq(FAWPLAM_E,
      `(&2 - (&999 / &1000 - ss / &2) * cc) - l +
       ((&999 / &1000 - ss / &2) * cc - &543 / &500) * r pow 2 -
       (&1 / &2 + (&999 / &1000) * ss - ss pow 2 / &2) * l * r`))
   SUBST1_TAC THENL
   [UNDISCH_TAC `l pow 2 + r pow 2 = &1` THEN
    UNDISCH_TAC `cc pow 2 + ss pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
   UNDISCH_TAC
    `&0 <= (l - (&5 / &4 - (&77 / &100) * r)) *
           (&1 + (&1 / &2 + (&999 / &1000) * ss - ss pow 2 / &2) * r)` THEN
   REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&999 / &1000 - ss / &2) * (cc - (&1 - (&51 / &100) * ss pow 2)) /\
    &0 <= ss * ss pow 2 /\
    &0 <= (ss - &1 / &20) * (&1 / &4 - (&503 / &1000) * (ss + &1 / &20))`
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   REWRITE_TAC[REAL_LE_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):real->real->bool` (FAWPLAM_P `&1 / &2`) `&0`)
  ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (mk_binop `(<=):real->real->bool` (FAWPLAM_P `&71 / &100`) `&0`)
  ASSUME_TAC THENL
  [REWRITE_TAC[REAL_POW_2] THEN RULE_ASSUM_TAC(REWRITE_RULE[REAL_POW_2]) THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   (list_mk_conj
    [mk_binop `(<=):real->real->bool`
       (mk_binop `( * ):real->real->real` `&71 / &100 - r` (FAWPLAM_P `&1 / &2`)) `&0`;
     mk_binop `(<=):real->real->bool`
       (mk_binop `( * ):real->real->real` `r - &1 / &2` (FAWPLAM_P `&71 / &100`)) `&0`;
     `&0 <= (((&999 / &1000 - ss / &2) * cc - &543 / &500) +
             (&77 / &100) * (&1 / &2 + (&999 / &1000) * ss - ss pow 2 / &2)) *
            ((r - &1 / &2) * (&71 / &100 - r))`])
  STRIP_ASSUME_TAC THENL
  [REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FAWPLAM_MUL_NONPOS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC FAWPLAM_MUL_NONPOS THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC]];
   ALL_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    let t = concl th in
    can (find_term ((=) `&77 / &100`)) t || can (find_term ((=) `&71 / &100`)) t)) THEN
  REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC);;

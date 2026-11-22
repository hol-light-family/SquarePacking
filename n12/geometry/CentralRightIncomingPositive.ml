(* ========================================================================= *)
(* Port of Compact/Geometry/CentralRightIncomingPositive.lean (Jatloe,       *)
(* N12-jatloe; namespace N12Compact.CentralRightIncomingPositive).  The      *)
(* other incoming central axis, with a nonnegative test direction and a     *)
(* nonpositive southeast central frame.  Normal is c977cc_normal; lower is   *)
(* ABT_lower (ABTransverse.ml), lower_in_bands C977NCO_LOWER_IN_BANDS.       *)
(* A square B with B.s = -t is c s u v a with the hypothesis s = --t.  The  *)
(* Lean local abbreviations dx, dy, K, H are written out.  Tag CRIP_.        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/ABTransverse.ml";;
needs "n12/geometry/C977NegativeCorner.ml";;

let CRIP_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let CRIP_SPLIT_TAC =
  REPEAT(FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC o check (is_conj o concl)));;

let CRIP_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

(* Lean: margin (private) *)
let CRIP_MARGIN = prove
 (`forall C S c t. c977cc_normal C S /\ c977cc_normal c t
     ==> (C * c - S * t) * (&3 * c - &2 * t - &1) +
         (C * t + S * c) * ((&33 / &20) * c + (&47 / &20) * t) <= &2 * (C + S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CRIP_NORMAL_TAC THEN
  CRIP_PROD_TAC `&1 - c` `(&13 / &20) * c - &7 / &20` THEN
  CRIP_PROD_TAC `c:real` `t:real` THEN
  SUBGOAL_THEN `&1 - c - (&13 / &20) * t pow 2 - (&7 / &20) * c * t <= &0` ASSUME_TAC THENL
  [SUBGOAL_THEN `&1 - c - (&13 / &20) * t pow 2 - (&7 / &20) * c * t =
                 (&1 - c) * ((&7 / &20) - (&13 / &20) * c) - (&7 / &20) * c * t`
     SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
    NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
  CRIP_PROD_TAC `c - t` `&1 - (&13 / &20) * c + (&7 / &20) * t` THEN
  SUBGOAL_THEN `(&1 - c - (&13 / &20) * t pow 2 - (&7 / &20) * c * t) +
                (--(&7 / &20) + (&7 / &20) * t pow 2 - (&13 / &20) * c * t + t) <= &0`
    ASSUME_TAC THENL
  [SUBGOAL_THEN `(&1 - c - (&13 / &20) * t pow 2 - (&7 / &20) * c * t) +
                 (--(&7 / &20) + (&7 / &20) * t pow 2 - (&13 / &20) * c * t + t) =
                 --(c - t) * (&1 - (&13 / &20) * c + (&7 / &20) * t)` SUBST1_TAC THENL
   [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING;
    NLIN_TAC ~deg2:false []]; ALL_TAC] THEN
  CRIP_PROD_TAC `C - S` `--(&1 - c - (&13 / &20) * t pow 2 - (&7 / &20) * c * t)` THEN
  CRIP_PROD_TAC `S:real`
    `--((&1 - c - (&13 / &20) * t pow 2 - (&7 / &20) * c * t) +
        (--(&7 / &20) + (&7 / &20) * t pow 2 - (&13 / &20) * c * t + t))` THEN
  SUBGOAL_THEN
   `(C * c - S * t) * (&3 * c - &2 * t - &1) +
    (C * t + S * c) * ((&33 / &20) * c + (&47 / &20) * t) - &2 * (C + S) =
    C * (&1 - c - (&13 / &20) * t pow 2 - (&7 / &20) * c * t) +
    S * (--(&7 / &20) + (&7 / &20) * t pow 2 - (&13 / &20) * c * t + t)` ASSUME_TAC THENL
  [UNDISCH_TAC `c pow 2 + t pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: upper_u_bound *)
let CRIP_UPPER_U_BOUND = prove
 (`forall c s u v a t C S.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C S /\ c977cc_normal c t /\ s = --t /\ &1 <= a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     u + a <= &3 * c - &2 * t
     ==> ABT_lower c s u v a C S <= &2 * (C + S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `c:real`; `t:real`] CRIP_MARGIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  CRIP_NORMAL_TAC THEN
  CRIP_PROD_TAC `c:real` `C - S` THEN CRIP_PROD_TAC `S:real` `c - t` THEN
  SUBGOAL_THEN `&0 <= C * c - S * t` ASSUME_TAC THENL
  [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= C * t + S * c` ASSUME_TAC THENL
  [MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `ABT_lower c (--t) u v a C S = (C * c - S * t) * u + (C * t + S * c) * v`
    SUBST1_TAC THENL
  [REWRITE_TAC[C977NCO_LOWER_IN_BANDS] THEN
   REWRITE_TAC[REAL_ARITH `C * c + S * --t = C * c - S * t`;
               REAL_ARITH `--C * --t + S * c = C * t + S * c`] THEN
   ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[linside; REAL_NEG_NEG]) THEN CRIP_SPLIT_TAC THEN
  CRIP_PROD_TAC `C * c - S * t` `&3 * c - &2 * t - &1 - u` THEN
  CRIP_PROD_TAC `C * t + S * c` `(&33 / &20) * c + (&47 / &20) * t - v` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: lower_escape_point *)
let CRIP_LOWER_ESCAPE_POINT = prove
 (`forall c s u v a t C S.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal C S /\ c977cc_normal c t /\ s = --t /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&87 / &50) /\ c + &3 * t <= v /\
     &2 * (C + S) < ABT_lower c s u v a C S
     ==> linside c s u v a (&3) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `linside c s u v a (&3) (&2)` THENL
  [FIRST_ASSUM ACCEPT_TAC; MATCH_MP_TAC(TAUT `false ==> p`)] THEN
  SUBGOAL_THEN `u + a <= &3 * c - &2 * t` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (&3) (&2)` THEN REWRITE_TAC[] THEN
   CRIP_NORMAL_TAC THEN
   FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
   RULE_ASSUM_TAC(REWRITE_RULE[linside]) THEN CRIP_SPLIT_TAC THEN REWRITE_TAC[linside] THEN
   RASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `t:real`; `C:real`; `S:real`]
    CRIP_UPPER_U_BOUND) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  RASM_ARITH_TAC);;

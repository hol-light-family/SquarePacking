(* ========================================================================= *)
(* Port of Compact/Geometry/FourSquareBCorner.lean                           *)
(* (N12Compact.FourSquareBCorner).  The failed horizontal section of B       *)
(* forces its two upper faces into one corner and a large positive angle.    *)
(*                                                                           *)
(* LongSection q h = scap_longsec (SectionCapacity.ml); sectionRadius =      *)
(* lsec_radius (LongSection.ml); supportRadius = tss_support_radius.         *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/FourSquareAForced.ml";;
needs "n12/geometry/LongSection.ml";;
needs "n12/geometry/ThreeSquareSupport.ml";;

(* REAL_ARITH with the (conjunctions of) real-relation assumptions *)
let FSBC_ARITH_TAC (asl,w as g) =
  let hs = filter (fun th -> let t = concl th in
                     is_real_rel t || (is_neg t && is_real_rel (rand t)))
                  (flat (map (CONJUNCTS o snd) asl)) in
  (if hs = [] then REAL_ARITH_TAC else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

(* use the negated-membership assumption mentioning all the given subterms *)
let FSBC_MISS_TAC pats =
  FIRST_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) &&
    forall (fun p -> can (find_term ((=) p)) (concl th)) pats)) THEN
  REWRITE_TAC[] THEN FSBC_ARITH_TAC;;

(* Lean: canonical_bounds *)
let FSBC_CANONICAL_BOUNDS = prove
 (`forall c s. c * c + s * s = &1 /\ &0 <= c /\ &0 <= s /\ s <= c
     ==> &7 / &10 <= c /\ c <= &1 /\ s <= &1 /\
         c + s <= &10 / &7 /\ c * s <= &1 / &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c:real`; SQ_NONNEG `s:real`; SQ_NONNEG `c - s`]
   [`c <= &1`; `s <= &1`; `c * s <= &1 / &2`; `&0 <= (c - s) * (c + s)`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  NLIN_TAC [SQ_NONNEG `c - s`]);;

(* Lean: no_long_section *)
let FSBC_NO_LONG_SECTION = prove
 (`forall cA sA uA vA aA cB sB uB vB aB cL sL uL vL aL cR sR uR vR aR.
     cL * cL + sL * sL = &1 /\ &0 < aL /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     lcont cB sB uB vB aB /\
     lclosed cL sL uL vL aL (&1) (&12 / &5) /\
     linside cA sA uA vA aA (&2) (&12 / &5) /\
     lclosed cR sR uR vR aR (&3) (&12 / &5) /\
     ldisj cB sB uB vB aB cL sL uL vL aL /\
     ldisj cB sB uB vB aB cA sA uA vA aA /\
     ldisj cB sB uB vB aB cR sR uR vR aR
     ==> ~scap_longsec cB sB uB vB aB (&12 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `&12 / &5`]
    SCAP_SECTION_HITS) THEN
  ASM_REWRITE_TAC[ARITH_RULE `j < 3 <=> j = 0 \/ j = 1 \/ j = 2`] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THENL
   [MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cL:real`; `sL:real`; `uL:real`; `vL:real`; `aL:real`;
                  `&1`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
    ASM_REWRITE_TAC[GSYM ldisj];
    RULE_ASSUM_TAC(REWRITE_RULE[ldisj]) THEN ASM_MESON_TAC[];
    MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`;
                  `cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                  `&3`; `&12 / &5`] OUTSIDE_OF_CLOSED) THEN
    ASM_REWRITE_TAC[GSYM ldisj]]);;

(* Lean: center_above_radius *)
let FSBC_CENTER_ABOVE_RADIUS = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 <= c /\ &0 <= s /\ s <= c /\ &1 < a /\ a <= &1001 / &1000 /\
     lclosed c s u v a (&8 / &5) (&3) /\
     ~scap_longsec c s u v a (&12 / &5)
     ==> &12 / &5 + (c + s - &2 * c * s) / &2 < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FSBC_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`; `&8 / &5`; `&3`;
                `&0`; `&1`] TSS_CLOSED_SUPPORT) THEN
  ASM_REWRITE_TAC[tss_support_radius] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_MUL_LID; REAL_ADD_LID; REAL_NEG_0] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `a * (c + s) <= &1001 / &1000 * (c + s)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN FSBC_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&12 / &5 - (c + s - &2 * c * s) / &2 <= lcy c s u v a` ASSUME_TAC THENL
   [UNDISCH_TAC `abs(&3 - lcy c s u v a) <= a / &2 * (s + c)` THEN
    FSBC_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  UNDISCH_TAC `~scap_longsec c s u v a (&12 / &5)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC LSEC_HORIZONTAL_LONG_SECTION THEN
  ASM_REWRITE_TAC[lsec_radius] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 <= x ==> abs x = x`; REAL_LE_MUL] THEN
  FSBC_ARITH_TAC);;

(* Lean: upper_corner *)
let FSBC_UPPER_CORNER = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ &0 <= s /\ s <= c /\ &1 < a /\ a <= &1001 / &1000 /\
     lclosed c s u v a (&33 / &20) (&47 / &20) /\
     lclosed c s u v a (&8 / &5) (&3) /\
     lclosed c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&1) (&1543 / &500) /\
     ~linside c s u v a (&2) (&1543 / &500) /\
     ~scap_longsec c s u v a (&12 / &5)
     ==> u + a <= &2 * c + (&1543 / &500) * s /\
         v + a <= --s + (&1543 / &500) * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FSBC_CANONICAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FSBC_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`]
    FSBC_CENTER_ABOVE_RADIUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FSBC_ARITH_TAC; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside; lcy]) THEN
  SUBGOAL_THEN `c + s * (&1543 / &500) <= u \/
                v + a <= --s + c * (&1543 / &500)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
    FSBC_MISS_TAC [`c * &1`; `&1543 / &500`]; ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= &2 * c + s * (&1543 / &500) \/
                v + a <= -- &2 * s + c * (&1543 / &500)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT; GSYM DE_MORGAN_THM] THEN STRIP_TAC THEN
    FSBC_MISS_TAC [`c * &2`; `&1543 / &500`]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v + a <= -- &2 * s + c * (&1543 / &500))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `&130 * s <= &43 * c` ASSUME_TAC THENL [FSBC_ARITH_TAC; ALL_TAC] THEN
    NLIN_FACTS_TAC [SQ_NONNEG `s:real`]
     [`&47 / &50 <= c`; `c * s <= &43 / &130`;
      `s * u <= s * (c * &87 / &50 + s * &3)`;
      `c * (v + a) <= c * (-- &2 * s + c * (&1543 / &500))`;
      `&0 <= (a - &1) * (c - s)`] THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN `u + a <= &2 * c + s * (&1543 / &500)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [FSBC_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    rand(lhand(concl th)) = `u:real`)) THEN
  FSBC_ARITH_TAC);;

(* Lean: corner_steep *)
let FSBC_CORNER_STEEP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 <= c /\ &0 <= s /\ s <= c /\ &1 < a /\
     &12 / &5 + (c + s - &2 * c * s) / &2 < lcy c s u v a /\
     u + a <= &2 * c + (&1543 / &500) * s /\
     v + a <= --s + (&1543 / &500) * c
     ==> &5 / &4 < c + s /\ &9 / &32 < s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FSBC_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcy]) THEN
  NLIN_FACTS_TAC []
   [`s * (u + a) <= s * (&2 * c + (&1543 / &500) * s)`;
    `c * (v + a) <= c * (--s + (&1543 / &500) * c)`;
    `&0 <= (a - &1) * (c + s)`] THEN
  NLIN_FACTS_TAC []
   [`c + s - &2 * c * s < &343 / &500`; `&0 <= c * s`] THEN
  NLIN_FACTS_TAC [] [`&1 <= c + s`] THEN
  SUBGOAL_THEN `&5 / &4 < c + s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC [] [`&0 <= (c + s - &1) * (&5 / &4 - (c + s))`] THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c + s - &5 / &4`] [`&9 / &32 < c * s`; `c * s <= s`] THEN
  CONJ_TAC THEN FSBC_ARITH_TAC);;

(* Lean: forced_lower_V *)
let FSBC_FORCED_LOWER_V = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\
     &0 < c /\ &0 <= s /\ s <= c /\ &1 < a /\ &9 / &32 < s /\
     lclosed c s u v a (&33 / &20) (&47 / &20) /\
     lclosed c s u v a (&8 / &5) (&3) /\
     lclosed c s u v a (&87 / &50) (&3) /\
     ~linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&2) (&5 / &2) /\
     v + a <= --s + (&1543 / &500) * c
     ==> -- &2 * s + (&5 / &2) * c <= v /\
         a <= s + (&293 / &500) * c /\ &34 / &25 < c + s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] FSBC_CANONICAL_BOUNDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN FSBC_ARITH_TAC; STRIP_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lclosed; linside]) THEN
  SUBGOAL_THEN `c + s * (&12 / &5) <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `v + a <= --s + c * (&12 / &5)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      FSBC_MISS_TAC [`c * &1`; `&12 / &5`]; ALL_TAC] THEN
    FSBC_MISS_TAC [`c * &2`; `&5 / &2`]; ALL_TAC] THEN
  SUBGOAL_THEN `c + s / &10 < &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= (c - (&1 - s / &10)) * (c + (&1 - s / &10))`;
      `&0 < s * ((&101 / &100) * s - &1 / &5)`] THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  SUBGOAL_THEN `-- &2 * s + (&5 / &2) * c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    FSBC_MISS_TAC [`c * &2`; `&5 / &2`]; ALL_TAC] THEN
  SUBGOAL_THEN `a <= s + (&293 / &500) * c` ASSUME_TAC THENL
   [FSBC_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&19 / &50 < c - s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    NLIN_FACTS_TAC []
     [`&0 <= (&34 / &25 - (c + s)) * (&34 / &25 + (c + s))`;
      `&0 <= (&19 / &50 - (c - s)) * (&19 / &50 + (c - s))`] THEN
    NLIN_TAC [];
    ALL_TAC] THEN
  FSBC_ARITH_TAC);;

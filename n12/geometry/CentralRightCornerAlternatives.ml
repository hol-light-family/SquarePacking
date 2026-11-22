(* ========================================================================= *)
(* Port of Compact/Geometry/CentralRightCornerAlternatives.lean (Jatloe,     *)
(* N12-jatloe; namespace N12Compact.CentralRightCornerAlternatives).         *)
(* The genuine lower-V escape of a negative southeast central frame is       *)
(* retained.  Normal is c977cc_normal; |B.s| <= B.c is abs sB <= cB;         *)
(* PairedCornerPositiveWall.negative_right_point: PCPW_NEGATIVE_RIGHT_POINT. *)
(* The OpenSquare invariants are explicit hypotheses.                        *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/PairedCornerPositiveWall.ml";;

let CRCA_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let CRCA_IN_TAC t = STRIP_ASSUME_TAC(REWRITE_RULE[linside] (ASSUME t));;

(* Lean: canonical_bounds (private) *)
let CRCA_CANONICAL_BOUNDS = prove
 (`forall c s. c * c + s * s = &1 /\ abs s <= c ==> &0 < c /\ c <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN CONJ_TAC THENL
  [NLIN_TAC []; NLIN_TAC [SQ_NONNEG `c - &1`; SQ_NONNEG `s:real`]]);;

(* Lean: canonical_corner_faces *)
let CRCA_CANONICAL_CORNER_FACES = prove
 (`forall c s u v a. abs s <= c /\ linside c s u v a (&47 / &20) (&33 / &20) /\
               ~linside c s u v a (&3) (&1)
     ==> u + a <= &3 * c + s \/ c - &3 * s <= v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[REAL_ABS_BOUNDS] THEN STRIP_TAC THEN
  CRCA_IN_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
  UNDISCH_TAC `~linside c s u v a (&3) (&1)` THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* Lean: canonical_lower_escape_point *)
let CRCA_CANONICAL_LOWER_ESCAPE_POINT = prove
 (`forall c s u v a. c * c + s * s = &1 /\ abs s <= c /\ &1 < a /\
               linside c s u v a (&47 / &20) (&33 / &20) /\
               linside c s u v a (&3) (&87 / &50) /\
               &2 * (c + s) <= u /\ c - &3 * s <= v
     ==> linside c s u v a (&3) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`] CRCA_CANONICAL_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
  CRCA_IN_TAC `linside c s u v a (&47 / &20) (&33 / &20)` THEN
  CRCA_IN_TAC `linside c s u v a (&3) (&87 / &50)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: corner_faces *)
let CRCA_CORNER_FACES = prove
 (`forall c s u v a t. c977cc_normal c t /\ s = --t /\
                 linside c s u v a (&47 / &20) (&33 / &20) /\
                 ~linside c s u v a (&3) (&1)
     ==> u + a <= &3 * c - t \/ c + &3 * t <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  CRCA_NORMAL_TAC THEN
  CRCA_IN_TAC `linside c (--t) u v a (&47 / &20) (&33 / &20)` THEN
  UNDISCH_TAC `~linside c (--t) u v a (&3) (&1)` THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* Lean: lower_escape_point *)
let CRCA_LOWER_ESCAPE_POINT = prove
 (`forall c s u v a t. c977cc_normal c t /\ s = --t /\ &1 < a /\
                 linside c s u v a (&47 / &20) (&33 / &20) /\
                 &2 * (c - t) <= u /\ c + &3 * t <= v
     ==> linside c s u v a (&3) (&2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s = --t`)) THEN
  CRCA_NORMAL_TAC THEN
  CRCA_IN_TAC `linside c (--t) u v a (&47 / &20) (&33 / &20)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: positive_wall_missing *)
let CRCA_POSITIVE_WALL_MISSING = prove
 (`forall c s u v a. c977cc_normal c s /\
               linside c s u v a (&1543 / &500) (&2) /\ linside c s u v a (&3) (&12 / &5) /\
               ~linside c s u v a (&3) (&2)
     ==> &3 * c + &2 * s <= u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CRCA_NORMAL_TAC THEN
  CRCA_IN_TAC `linside c s u v a (&1543 / &500) (&2)` THEN
  CRCA_IN_TAC `linside c s u v a (&3) (&12 / &5)` THEN
  UNDISCH_TAC `~linside c s u v a (&3) (&2)` THEN REWRITE_TAC[linside] THEN
  RASM_ARITH_TAC);;

(* the common right-wall step of both alternatives *)
let CRCA_RIGHT_TAC =
  ASM_CASES_TAC `&0 <= sR` THENL
  [ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`]
     CRCA_POSITIVE_WALL_MISSING) THEN
   ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN RASM_ARITH_TAC;
   MATCH_MP_TAC(TAUT `false ==> p`) THEN
   UNDISCH_TAC `~linside cR sR uR vR aR (&3) (&2)` THEN REWRITE_TAC[] THEN
   MATCH_MP_TAC(SPECL [`cR:real`; `sR:real`; `uR:real`; `vR:real`; `aR:real`;
                       `cE:real`; `sE:real`; `uE:real`; `vE:real`; `aE:real`; `--sR`]
     PCPW_NEGATIVE_RIGHT_POINT) THEN
   ASM_REWRITE_TAC[c977cc_normal; REAL_NEG_NEG; REAL_POW_2] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[REAL_ABS_BOUNDS]) THEN
   REPEAT(FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl))) THEN
   REPEAT CONJ_TAC THEN RASM_ARITH_TAC];;

(* Lean: canonical_alternatives *)
let CRCA_CANONICAL_ALTERNATIVES = prove
 (`forall cB sB uB vB aB cR sR uR vR aR cE sE uE vE aE.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cE * cE + sE * sE = &1 /\ &0 < aE /\
     abs sB <= cB /\ abs sR <= cR /\ &1 < aB /\ &1 < aR /\ lcont cR sR uR vR aR /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\
     linside cB sB uB vB aB (&3) (&87 / &50) /\ ~linside cB sB uB vB aB (&3) (&1) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\ linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&1543 / &500) (&3) /\
     linside cE sE uE vE aE (&3) (&1543 / &500) /\
     ldisj cB sB uB vB aB cR sR uR vR aR /\ ldisj cE sE uE vE aE cR sR uR vR aR /\
     &2 * (cB + sB) <= uB
     ==> (sB < &0 /\ uB + aB <= &3 * cB + sB) \/
         (&0 <= sR /\ &3 * cR + &2 * sR <= uR)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    CRCA_CANONICAL_CORNER_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
  [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
   MP_TAC(SPECL [`cB:real`; `sB:real`] CRCA_CANONICAL_BOUNDS) THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC;
   ALL_TAC] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    CRCA_CANONICAL_LOWER_ESCAPE_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~linside cR sR uR vR aR (&3) (&2)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cB sB uB vB aB cR sR uR vR aR` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&3`; `&2`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISJ2_TAC THEN CRCA_RIGHT_TAC);;

(* Lean: alternatives *)
let CRCA_ALTERNATIVES = prove
 (`forall cB sB uB vB aB cR sR uR vR aR cE sE uE vE aE t.
     cB * cB + sB * sB = &1 /\ &0 < aB /\ cR * cR + sR * sR = &1 /\ &0 < aR /\
     cE * cE + sE * sE = &1 /\ &0 < aE /\
     c977cc_normal cB t /\ sB = --t /\ abs sR <= cR /\ &1 < aB /\ &1 < aR /\
     lcont cR sR uR vR aR /\
     linside cB sB uB vB aB (&47 / &20) (&33 / &20) /\ ~linside cB sB uB vB aB (&3) (&1) /\
     linside cR sR uR vR aR (&1543 / &500) (&2) /\ linside cR sR uR vR aR (&3) (&12 / &5) /\
     linside cE sE uE vE aE (&16 / &5) (&3) /\ linside cE sE uE vE aE (&3) (&3) /\
     linside cE sE uE vE aE (&1543 / &500) (&3) /\
     linside cE sE uE vE aE (&3) (&1543 / &500) /\
     ldisj cB sB uB vB aB cR sR uR vR aR /\ ldisj cE sE uE vE aE cR sR uR vR aR /\
     &2 * (cB - t) <= uB
     ==> uB + aB <= &3 * cB - t \/ (&0 <= sR /\ &3 * cR + &2 * sR <= uR)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`]
    CRCA_CORNER_FACES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`; `t:real`]
    CRCA_LOWER_ESCAPE_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~linside cR sR uR vR aR (&3) (&2)` ASSUME_TAC THENL
  [UNDISCH_TAC `ldisj cB sB uB vB aB cR sR uR vR aR` THEN REWRITE_TAC[ldisj] THEN
   DISCH_THEN(MP_TAC o SPECL [`&3`; `&2`]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISJ2_TAC THEN CRCA_RIGHT_TAC);;

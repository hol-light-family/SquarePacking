(* ========================================================================= *)
(* Port of Compact/Geometry/PositiveWallEscapeFaces.lean (Jatloe, N12-jatloe)*)
(* (namespace N12Compact.PositiveWallEscapeFaces).                           *)
(* Positive left-wall face reduction in the central escape.                  *)
(* FourSquareBLBridge.left_wall is FSBL_LEFT_WALL.                           *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/C977CornerCubic.ml";;
needs "n12/geometry/PositiveCentralNegativeFloor.ml";;
needs "n12/geometry/FourSquareBLBridge.ml";;

let PWEF_NORMAL_TAC =
  ASSUM_LIST (fun ths ->
    let ns = filter (can (term_match [] `c977cc_normal x y`) o concl) ths in
    MAP_EVERY (fun th -> STRIP_ASSUME_TAC (MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                         STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal] th)) ns);;

let PWEF_PROD_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LE_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;
let PWEF_PRODLT_TAC a b =
  MP_TAC(SPECL [a; b] REAL_LT_MUL) THEN
  ANTS_TAC THENL [CONJ_TAC THEN RASM_ARITH_TAC; DISCH_TAC];;

let PWEF_USE th tms =
  MP_TAC(SPECL tms th) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
                  DISCH_THEN(STRIP_ASSUME_TAC)];;

let PWEF_BAND_TAC tm =
  MP_TAC(ASSUME tm) THEN REWRITE_TAC[linside] THEN STRIP_TAC;;

(* Lean: upper_faces *)
let PWEF_UPPER_FACES = prove
 (`forall c s u v a. c977cc_normal c s /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&72 / &25)
     ==> u + a <= c + (&72 / &25) * s \/ v + a <= (&72 / &25) * c - s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWEF_NORMAL_TAC THEN
  PWEF_BAND_TAC `linside c s u v a (&1) (&12 / &5)` THEN
  UNDISCH_TAC `~linside c s u v a (&1) (&72 / &25)` THEN
  REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: lower_face *)
let PWEF_LOWER_FACE = prove
 (`forall cA sA uA vA aA c s u v a.
     c977cc_normal c s /\ &1 < a /\ linside cA sA uA vA aA (&6 / &5) (&2) /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&72 / &25) /\ ~linside c s u v a (&19 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA c s u v a
     ==> (&187 / &100) * c - (&19 / &25) * s <= v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] PWEF_UPPER_FACES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  PWEF_NORMAL_TAC THEN
  PWEF_BAND_TAC `linside c s u v a (&457 / &500) (&2)` THEN
  PWEF_BAND_TAC `linside c s u v a (&1) (&12 / &5)` THEN
  REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(&19 / &25) * c + (&187 / &100) * s <= u` ASSUME_TAC THENL
  [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
   UNDISCH_TAC `~linside c s u v a (&19 / &25) (&187 / &100)` THEN
   REWRITE_TAC[linside] THEN RASM_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
  [RASM_ARITH_TAC; ALL_TAC] THEN
  NLIN_FACTS_TAC [SQ_NONNEG `c - &11 / &25`; SQ_NONNEG `s - &13 / &100`;
                  SQ_NONNEG `c - &22 / &25`; SQ_NONNEG `s - &1 / &5`]
    [`(&11 / &25) * c + (&13 / &100) * s < &1`;
     `(&22 / &25) * c + (&1 / &5) * s < &1`] THEN
  UNDISCH_TAC `ldisj cA sA uA vA aA c s u v a` THEN
  REWRITE_TAC[ldisj] THEN DISCH_THEN(MP_TAC o SPECL [`&6 / &5`; `&2`]) THEN
  ASM_REWRITE_TAC[linside] THEN RASM_ARITH_TAC);;

(* Lean: upper_u_tilt (private) *)
let PWEF_UPPER_U_TILT = prove
 (`forall c s u v a.
     c977cc_normal c s /\ &1 < a /\ lcont c s u v a /\
     (&187 / &100) * c - (&19 / &25) * s <= v /\ u + a <= c + (&72 / &25) * s
     ==> s < &3 / &5`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN PWEF_NORMAL_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] FSBL_LEFT_WALL) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY RASM_ARITH_TAC THEN
   UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; DISCH_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[lcx]) THEN
  SUBGOAL_THEN `abs s = s` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THENL
  [ASM_REWRITE_TAC[REAL_ABS_REFL]; ALL_TAC] THEN
  SUBGOAL_THEN `s * (v + a) <= c * u` ASSUME_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  PWEF_PROD_TAC `s:real` `v - ((&187 / &100) * c - (&19 / &25) * s)` THEN
  PWEF_PROD_TAC `c:real` `(c + (&72 / &25) * s) - (u + a)` THEN
  PWEF_PRODLT_TAC `a - &1` `c + s` THEN
  SUBGOAL_THEN `c + s - &1 - (&101 / &100) * c * s + (&6 / &25) * s pow 2 < &0`
  ASSUME_TAC THENL [NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  ABBREV_TAC `K = (c + &4 / &5) * (&24 / &125 + (&6 / &25) * (s + &3 / &5)) -
                  (s + &3 / &5) * (&1 - (&101 / &100) * s)` THEN
  PWEF_PROD_TAC `c - &7 / &10` `&24 / &125 + (&6 / &25) * (s + &3 / &5)` THEN
  PWEF_PROD_TAC `s + &3 / &5` `&197 / &500 - (&1 - (&101 / &100) * s)` THEN
  SUBGOAL_THEN `&0 <= K` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN NLIN_TAC ~deg2:false []; ALL_TAC] THEN
  PWEF_PROD_TAC `s - &3 / &5` `K:real` THEN
  SUBGOAL_THEN
   `(c + &4 / &5) * (c + s - &1 - (&101 / &100) * c * s + (&6 / &25) * s pow 2 - &1 / &625) =
    (s - &3 / &5) * K` ASSUME_TAC THENL
  [EXPAND_TAC "K" THEN UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING;
   ALL_TAC] THEN
  PWEF_PRODLT_TAC `c + &4 / &5`
    `--(c + s - &1 - (&101 / &100) * c * s + (&6 / &25) * s pow 2 - &1 / &625)` THEN
  NLIN_TAC ~deg2:false []);;

(* Lean: faces *)
let PWEF_FACES = prove
 (`forall cA sA uA vA aA c s u v a.
     c977cc_normal c s /\ &1 < a /\ lcont c s u v a /\
     linside cA sA uA vA aA (&6 / &5) (&2) /\
     linside c s u v a (&457 / &500) (&2) /\ linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&72 / &25) /\ ~linside c s u v a (&19 / &25) (&187 / &100) /\
     ldisj cA sA uA vA aA c s u v a
     ==> (&187 / &100) * c - (&19 / &25) * s <= v /\
         ((u + a <= c + (&72 / &25) * s /\ s < &3 / &5) \/
          (v + a <= (&72 / &25) * c - s /\ s < &1 / &24))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  PWEF_USE PWEF_LOWER_FACE
    [`cA:real`; `sA:real`; `uA:real`; `vA:real`; `aA:real`;
     `c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THEN
  ASM_REWRITE_TAC[] THEN
  PWEF_USE PWEF_UPPER_FACES [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] THENL
  [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PWEF_UPPER_U_TILT THEN
   MAP_EVERY EXISTS_TAC [`c:real`; `u:real`; `v:real`; `a:real`] THEN ASM_REWRITE_TAC[];
   DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN PWEF_NORMAL_TAC THEN RASM_ARITH_TAC]);;

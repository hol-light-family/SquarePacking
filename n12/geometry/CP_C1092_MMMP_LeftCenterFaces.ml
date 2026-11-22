(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/LeftCenterFaces.lean                 *)
(* (namespace N12Compact.C1092MMMPLeftCenterFaces).                          *)
(* centerX / centerY are lcx / lcy; Normal is c977cc_normal.                 *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WholeSupports.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MLCF_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092MLCF_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MLCF_LIN_TAC;;

let C1092MLCF_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092MLCF_MISS_TAC x y; ALL_TAC];;

let C1092MLCF_PROD_TAC tms =
  MAP_EVERY (fun t -> SUBGOAL_THEN t ASSUME_TAC THENL
    [(MATCH_MP_TAC REAL_LE_MUL ORELSE MATCH_MP_TAC REAL_LT_MUL) THEN
     REPEAT CONJ_TAC THEN C1092MLCF_LIN_TAC; ALL_TAC]) tms;;

let C1092MLCF_PREP_TAC =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] LCENTRE_COORDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[lcy] o check
    (fun th -> concl th = `&0 <= lcy c s u v a`)) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th
                           else REWRITE_RULE[linside; c977cc_normal] th);;

(* Lean: positive (origin_faces is the unfolding of linside at the origin) *)
let C1092MLCF_POSITIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c s /\ &1 < a /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (&0) (&39 / &100) /\
     ~linside c s u v a (&0) (&1 / &2) /\ ~linside c s u v a (&1 / &2) (&0) /\
     &0 <= lcy c s u v a
     ==> &0 < s /\ u + a <= s / &2 /\ lcx c s u v a < &0`,
  C1092MLCF_PREP_TAC THEN
  SUBGOAL_THEN `u + a <= s / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MLCF_FACT_TAC `v + a <= c / &2` `&0` `&1 / &2` THEN
    ASM_CASES_TAC `u + a <= c / &2` THENL
     [C1092MLCF_PROD_TAC [`&0 <= s * (c / &2 - (u + a))`;
                          `&0 <= c * (c / &2 - (v + a))`;
                          `&0 < (a - c) * (c + s)`] THEN
      NLIN_TAC ~deg2:false [];
      C1092MLCF_FACT_TAC `--s / &2 <= v` `&1 / &2` `&0` THEN C1092MLCF_LIN_TAC];
    ALL_TAC] THEN
  C1092MLCF_PROD_TAC [`&0 <= s * lcy c s u v a`] THEN
  SUBGOAL_THEN `c * lcx c s u v a < &0` ASSUME_TAC THENL
   [C1092MLCF_LIN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [C1092MLCF_LIN_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MLCF_PROD_TAC [`&0 <= c * lcx c s u v a`] THEN C1092MLCF_LIN_TAC);;

(* Lean: negative *)
let C1092MLCF_NEGATIVE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c (--s) /\ &1 < a /\
     linside c s u v a (&0) (&0) /\ linside c s u v a (&0) (&39 / &100) /\
     ~linside c s u v a (&0) (&1 / &2) /\ ~linside c s u v a (&1 / &2) (&0) /\
     &0 <= lcy c s u v a
     ==> &0 < --s /\ v + a <= c / &2 /\ lcx c s u v a < &0`,
  C1092MLCF_PREP_TAC THEN
  SUBGOAL_THEN `v + a <= c / &2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MLCF_FACT_TAC `s / &2 <= u` `&0` `&1 / &2` THEN
    ASM_CASES_TAC `u + a <= c / &2` THENL
     [C1092MLCF_LIN_TAC;
      C1092MLCF_FACT_TAC `v + a <= --s / &2` `&1 / &2` `&0` THEN
      C1092MLCF_PROD_TAC [`&0 <= --s * (u - s / &2)`;
                          `&0 <= c * (--s / &2 - (v + a))`;
                          `&0 < (a + s) * (c - s)`] THEN
      NLIN_TAC ~deg2:false []];
    ALL_TAC] THEN
  C1092MLCF_PROD_TAC [`&0 <= c * lcy c s u v a`] THEN
  SUBGOAL_THEN `--s * lcx c s u v a < &0` ASSUME_TAC THENL
   [C1092MLCF_LIN_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_CASES_TAC `s = &0` THENL
     [UNDISCH_TAC `--s * lcx c s u v a < &0` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      C1092MLCF_LIN_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  C1092MLCF_PROD_TAC [`&0 <= --s * lcx c s u v a`] THEN C1092MLCF_LIN_TAC);;

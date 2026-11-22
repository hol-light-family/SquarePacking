(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MMMP/NortheastNegativeFaces.lean          *)
(* (namespace N12Compact.C1092MMMPNortheastNegativeFaces).                   *)
(* ShortChordTable.steep: C1092SCT_STEEP; Normal: c977cc_normal.             *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_ShortChordTable.ml";;

let C1092MNNF_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092MNNF_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c (--(t:real)) u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MNNF_LIN_TAC;;

let C1092MNNF_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092MNNF_MISS_TAC x y; ALL_TAC];;

(* Lean: Faces (structure) *)
let c1092mnnf_faces = new_definition
 `c1092mnnf_faces (c:real) s u v a <=>
    --c + s <= u /\ u + a <= --(&39 / &100) * c /\
    v + a <= c + (&39 / &100) * s /\ &9 / &20 < --s /\ c < &9 / &10`;;

(* Lean: negative (private) *)
let C1092MNNF_NEGATIVE = prove
 (`forall c s u v a b t.
     c * c + s * s = &1 /\ &0 < a /\
     c = b /\ s = --t /\ c977cc_normal b t /\ &1 < a /\
     linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     linside c s u v a (--(&1)) (&13 / &50) /\
     linside c s u v a (--(&1)) (&2 / &5) /\
     ~linside c s u v a (--(&39 / &100)) (&0) /\
     ~linside c s u v a (--(&39 / &100)) (&1) /\
     ~linside c s u v a (--(&543 / &500)) (&0) /\
     ~linside c s u v a (--(&1)) (&1) /\
     ~linside c s u v a (--(&1 / &2)) (&0)
     ==> c1092mnnf_faces c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `c:real = (b:real)`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `s:real = --(t:real)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th
                           else REWRITE_RULE[linside; c977cc_normal] th) THEN
  C1092MNNF_FACT_TAC `v + a <= c - (&39 / &100) * t` `--(&39 / &100)` `&1` THEN
  SUBGOAL_THEN `u + a <= --(&39 / &100) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNNF_MISS_TAC `--(&39 / &100)` `&0`; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [C1092MNNF_LIN_TAC; ALL_TAC] THEN
  C1092MNNF_FACT_TAC `--(&543 / &500) * t <= v` `--(&543 / &500)` `&0` THEN
  SUBGOAL_THEN `--c - t <= u:real` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MNNF_FACT_TAC `v + a <= c - t:real` `--(&1)` `&1` THEN
    SUBGOAL_THEN `&0 < (&1 + c) * (c + (&43 / &500) * t - &1) /\
                  &0 <= t * (&1 - c)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_MUL; MATCH_MP_TAC REAL_LE_MUL] THEN
      C1092MNNF_LIN_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `t < &43 / &250` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= t * (t - &43 / &250)` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN C1092MNNF_LIN_TAC; ALL_TAC] THEN
      NLIN_TAC ~deg2:false []; ALL_TAC] THEN
    C1092MNNF_MISS_TAC `--(&1 / &2)` `&0`; ALL_TAC] THEN
  MP_TAC(SPECL [`c:real`; `t:real`; `a:real`] C1092SCT_STEEP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[c977cc_normal] THEN C1092MNNF_LIN_TAC; STRIP_TAC] THEN
  REWRITE_TAC[c1092mnnf_faces] THEN C1092MNNF_LIN_TAC);;

(* Lean: faces *)
let C1092MNNF_FACES = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c (--s) /\ &1 < a /\
     linside c s u v a (--(&7 / &20)) (&7 / &20) /\
     linside c s u v a (--(&1)) (&13 / &50) /\
     linside c s u v a (--(&1)) (&2 / &5) /\
     ~linside c s u v a (--(&39 / &100)) (&0) /\
     ~linside c s u v a (--(&39 / &100)) (&1) /\
     ~linside c s u v a (--(&543 / &500)) (&0) /\
     ~linside c s u v a (--(&1)) (&1) /\
     ~linside c s u v a (--(&1 / &2)) (&0)
     ==> c1092mnnf_faces c s u v a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC C1092MNNF_NEGATIVE THEN
  MAP_EVERY EXISTS_TAC [`c:real`; `--s:real`] THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMMissingPositiveFaces.lean             *)
(* (namespace N12Compact.C1092MPPMMissingPositiveFaces).                     *)
(* half / quarter_data: C1092WPS_half / C1092WPS_QUARTER_DATA;               *)
(* Normal: c977cc_normal.                                                    *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_C1092_WallProfileScalars.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

let C1092MMPF_LIN_TAC (asl,w as g) =
  let rec ok t = is_real_rel t || (is_neg t && is_real_rel (rand t)) ||
                 (is_conj t && ok (lhand t) && ok (rand t)) in
  let hs = filter (ok o concl) (map snd asl) in
  (if hs = [] then REAL_ARITH_TAC
   else MP_TAC (end_itlist CONJ hs) THEN REAL_ARITH_TAC) g;;

let C1092MMPF_MISS_TAC x y =
  UNDISCH_TAC (mk_neg(list_mk_comb(`linside c s u v a`,[x;y]))) THEN
  REWRITE_TAC[linside; DE_MORGAN_THM; REAL_NOT_LT] THEN C1092MMPF_LIN_TAC;;

let C1092MMPF_FACT_TAC t x y =
  SUBGOAL_THEN t ASSUME_TAC THENL [C1092MMPF_MISS_TAC x y; ALL_TAC];;

(* Lean: Inputs (structure) *)
let c1092mmpf_inputs = new_definition
 `c1092mmpf_inputs c s u v a <=>
    linside c s u v a (--(&7 / &20)) (--(&7 / &20)) /\
    linside c s u v a (--(&1)) (--(&13 / &50)) /\
    linside c s u v a (--(&1)) (--(&2 / &5)) /\
    linside c s u v a (--(&1)) (--(&1 / &2)) /\
    ~linside c s u v a (--(&1)) (--(&1)) /\
    ~linside c s u v a (--(&543 / &500)) (--(&1)) /\
    ~linside c s u v a (--(&543 / &500)) (&0) /\
    ~linside c s u v a (--(&13 / &50)) (&0) /\
    ~linside c s u v a (--(&14 / &25)) (--(&1)) /\
    ~linside c s u v a (--(&13 / &50)) (--(&1))`;;

(* Lean: Faces (structure) *)
let c1092mmpf_faces = new_definition
 `c1092mmpf_faces c s u v a <=>
    --c - s <= u /\ u + a <= --(&13 / &50) * c /\
    (&14 / &25) * s - c <= v /\ v + a <= (&543 / &500) * s /\
    &0 < s /\ &13 / &87 < C1092WPS_half c s /\ C1092WPS_half c s < &1 / &2 /\
    a <= (&37 / &50) * c + s /\ a <= c + (&263 / &500) * s`;;

(* Lean: short_after_thin_width (private) *)
let C1092MMPF_SHORT_AFTER_THIN_WIDTH = prove
 (`forall c s. c977cc_normal c s /\ &1 < c + (&43 / &500) * s
         ==> (&413 / &500) * c + s < &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  SUBGOAL_THEN `&0 < (c + (&43 / &500) * s - &1) * (c + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(c + (&43 / &500) * s - &1) * (c + &1) =
                s * ((&43 / &500) * (&1 + c) - s)` ASSUME_TAC THENL
   [UNDISCH_TAC `c pow 2 + s pow 2 = &1` THEN CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (&43 / &500) * (&1 + c) - s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= s * (s - (&43 / &500) * (&1 + c))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Lean: profile *)
let C1092MMPF_PROFILE = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     &1 < a /\ c977cc_normal c s /\ c1092mmpf_inputs c s u v a
     ==> c1092mmpf_faces c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> can (term_match [] `c977cc_normal x y`) (concl th))) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c1092mmpf_inputs] o
    check (fun th -> can (term_match [] `c1092mmpf_inputs c s u v a`) (concl th))) THEN
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th) THEN
  SUBGOAL_THEN `u + a <= --(&13 / &50) * c` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MMPF_FACT_TAC `v + a <= (&13 / &50) * s` `--(&13 / &50)` `&0` THEN
    SUBGOAL_THEN `--c - s <= u` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
      C1092MMPF_FACT_TAC `s - c <= v` `--(&1)` `--(&1)` THEN
      C1092MMPF_LIN_TAC; ALL_TAC] THEN
    C1092MMPF_FACT_TAC `u + a <= --(&13 / &50) * c - s` `--(&13 / &50)` `--(&1)` THEN
    C1092MMPF_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `v + a <= (&543 / &500) * s` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MMPF_FACT_TAC `--(&543 / &500) * c <= u` `--(&543 / &500)` `&0` THEN
    C1092MMPF_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `--c - s <= u` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MMPF_FACT_TAC `s - c <= v` `--(&1)` `--(&1)` THEN
    MP_TAC(SPECL [`c:real`; `s:real`] C1092MMPF_SHORT_AFTER_THIN_WIDTH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[c977cc_normal] THEN C1092MMPF_LIN_TAC; DISCH_TAC] THEN
    C1092MMPF_FACT_TAC `(&543 / &500) * s - c <= v` `--(&543 / &500)` `--(&1)` THEN
    C1092MMPF_LIN_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&14 / &25) * s - c <= v` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    C1092MMPF_FACT_TAC `u + a <= --(&14 / &25) * c - s` `--(&14 / &25)` `--(&1)` THEN
    C1092MMPF_LIN_TAC; ALL_TAC] THEN
  REPEAT(FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_neg(concl th) || is_conj(concl th)))) THEN
  MP_TAC(SPECL [`c:real`; `s:real`] C1092WPS_QUARTER_DATA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `C1092WPS_half c s < &1 / &2` MP_TAC THENL
   [REWRITE_TAC[C1092WPS_half] THEN
    SUBGOAL_THEN `&0 < &1 + c` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[c1092mmpf_faces] THEN
  SPEC_TAC(`C1092WPS_half c s`,`q:real`) THEN GEN_TAC THEN
  REPEAT STRIP_TAC THEN TRY C1092MMPF_LIN_TAC THEN
  SUBGOAL_THEN `&0 < (&1 + q pow 2) * ((&37 / &50) * c + s - &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MP_TAC(SPEC `q:real` REAL_LE_POW_2) THEN REAL_ARITH_TAC; C1092MMPF_LIN_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (&1 - q) * (&13 - &87 * q)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN C1092MMPF_LIN_TAC; ALL_TAC] THEN
  C1092MMPF_LIN_TAC);;

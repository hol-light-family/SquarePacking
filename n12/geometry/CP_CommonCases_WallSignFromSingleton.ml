(* ========================================================================= *)
(* Phase 2: Compact/Completion/CommonCases/WallSignFromSingleton.lean.       *)
(* A foreign singleton point fixes the wall centre sign; the wall then gives *)
(* its near chord.  Squares W are 5-tuples c s u v a; centerX/centerY are    *)
(* lcx/lcy; pullY/pullSwap are LINSIDE_PULLY/LINSIDE_PULLSW.                 *)
(* original_bottom / original_left_center (literal seed-point and marker     *)
(* checks) are producers wsfs_original_bottom / wsfs_original_left_center.  *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/WallSignChord.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;

(* Lean: center_pullY_y, center_pullSwap_y (S12) *)
let WSFS_LCY_PULLY = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcy c (--s) (u - &4 * s) (&4 * c - v - a) a = &4 - lcy c s u v a`,
  REWRITE_TAC[lcy] THEN CONV_TAC REAL_RING);;
let WSFS_LCY_PULLSW = prove
 (`forall c s u v a. lcy s c u (--v - a) a = lcx c s u v a`,
  REWRITE_TAC[lcy; lcx] THEN REAL_ARITH_TAC);;

(* Lean: left_center *)
let WSFS_LEFT_CENTER = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ (forall x y. linside c s u v a x y ==> &0 <= x) /\
     linside c s u v a (&457 / &500) (&2) /\ ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&1) (&87 / &50)
     ==> &2 < lcy c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`; `&113 / &50`] WSC_CHORD) THEN
  ASM_SIMP_TAC[WSFS_LCY_PULLY; LINSIDE_PULLY] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIRST [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]);;

(* Lean: left_chord *)
let WSFS_LEFT_CHORD = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ (forall x y. linside c s u v a x y ==> &0 <= x) /\
     linside c s u v a (&457 / &500) (&2) /\ ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&33 / &20) (&47 / &20) /\ ~linside c s u v a (&1) (&87 / &50)
     ==> &2 < lcy c s u v a /\
         forall y. &111 / &50 <= y /\ y <= &239 / &100 ==> linside c s u v a (&1) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 < lcy c s u v a` ASSUME_TAC THENL
   [MATCH_MP_TAC WSFS_LEFT_CENTER THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC WSC_CHORD THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Lean: bottom_center *)
let WSFS_BOTTOM_CENTER = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ (forall x y. linside c s u v a x y ==> &0 <= y) /\
     linside c s u v a (&2) (&457 / &500) /\ ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&87 / &50) (&1)
     ==> &2 < lcx c s u v a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`] WSFS_LEFT_CENTER) THEN
  REWRITE_TAC[LINSIDE_PULLSW; WSFS_LCY_PULLSW] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIRST [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]);;

(* Lean: bottom_chord *)
let WSFS_BOTTOM_CHORD = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ (forall x y. linside c s u v a x y ==> &0 <= y) /\
     linside c s u v a (&2) (&457 / &500) /\ ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\ ~linside c s u v a (&87 / &50) (&1)
     ==> &2 < lcx c s u v a /\
         forall x. &111 / &50 <= x /\ x <= &239 / &100 ==> linside c s u v a x (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&2 < lcx c s u v a` ASSUME_TAC THENL
   [MATCH_MP_TAC WSFS_BOTTOM_CENTER THEN ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`; `x:real`] WSC_CHORD) THEN
  REWRITE_TAC[LINSIDE_PULLSW; WSFS_LCY_PULLSW] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN FIRST [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]);;

(* Lean: bottom_near *)
let WSFS_BOTTOM_NEAR = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &1 < a /\ (forall x y. linside c s u v a x y ==> &0 <= y) /\
     linside c s u v a (&2) (&457 / &500) /\ ~linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&33 / &20) /\ ~linside c s u v a (&87 / &50) (&1)
     ==> linside c s u v a (&113 / &50) (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC_ALL WSFS_BOTTOM_CHORD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN CONV_TAC REAL_RAT_REDUCE_CONV);;


(* Lean: original_bottom, for a literal mask m (decide: (2,457/500) is a seed of m,
   markers 8, 9 not in m, m <> 1):
   |- !c1 c2 a b l fam. NPACK .. /\ IMAGE binarysum (FFP ..) = fam /\ m IN fam /\ 1 IN fam
        ==> &2 < lcx (owner m) /\ !x. &111/&50 <= x /\ x <= &239/&100 ==> linside (owner m) x (&1) *)
let wsfs_owner_args m = map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`;
                                  `b:num->real`; `l:real`; mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let wsfs_original m n lemma foreign marker misses wallk =
  if m = n then failwith "wsfs: mask equals the foreign mask" else
  let inm t = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral t), `fam:num->bool`) in
  let hyp = list_mk_conj [`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = fam`; inm m; inm n] in
  let h = ASSUME hyp in
  let [hnp; hrow; hm; hn] = CONJUNCTS h in
  let five = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  let pk th t = MP (SPECL (five @ [mk_small_numeral t]) th) hnp in
  let unit = pk OO_UNIT m and side = MP (SPECL five OO_SIDE) hnp and box = pk OO_BOX m in
  let args = wsfs_owner_args m in
  let lin_xy = list_mk_comb(`linside`, args @ [`x:real`; `y:real`]) in
  let comps = CONJUNCTS (MP (SPECL [`x:real`; `y:real`] (REWRITE_RULE[lcont] box)) (ASSUME lin_xy)) in
  let wall = GENL [`x:real`; `y:real`] (DISCH lin_xy (el wallk comps)) in
  let use th t = MP (SPECL OO_VARS th) (CONJ hnp (CONJ hrow (if t = m then hm else hn))) in
  let mk = use (oo_seed m marker) m in
  let miss = map (fun k -> use (oo_missing m k) m) misses in
  let fn = use (oo_seed n foreign) n in
  let ne = EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n))) in
  let d = MP (SPECL (OO_VARS @ [mk_small_numeral m; mk_small_numeral n]) OO_APART)
             (end_itlist CONJ [hnp; hrow; hm; hn; ne]) in
  let d2 = SPECL [fst foreign; snd foreign] (REWRITE_RULE[ldisj] d) in
  let a0 = lhand (rand (concl d2)) in
  let sing = NOT_INTRO (DISCH a0 (MP (NOT_ELIM d2) (CONJ (ASSUME a0) fn))) in
  let th = MP (SPECL (fst (chop_list 5 args)) lemma) (end_itlist CONJ ([unit; side; wall; mk] @ miss @ [sing])) in
  GENL OO_VARS (DISCH hyp th);;

let wsfs_original_bottom m =
  let args = wsfs_owner_args m in
  let lin x y = list_mk_comb(`linside`, args @ [x; y]) in
  let concl = mk_conj(mk_binop `(<):real->real->bool` `&2` (list_mk_comb(`lcx`, args)),
    mk_forall(`x:real`, mk_imp(`&111 / &50 <= x /\ x <= &239 / &100`, lin `x:real` `&1`))) in
  if not (exists (qeq (num 2, nlin_rat "457/500")) (seed_points m)) then failwith "wsfs: (2,457/500) not in seedPoints" else
  ignore concl; wsfs_original m 1 WSFS_BOTTOM_CHORD (`&87 / &50`, `&1`) (`&2`, `&457 / &500`) [8; 9] 2;;

(* Lean: original_left_center *)
let wsfs_original_left_center m =
  let args = wsfs_owner_args m in
  let concl = mk_binop `(<):real->real->bool` `&2` (list_mk_comb(`lcy`, args)) in
  if not (exists (qeq (nlin_rat "457/500", num 2)) (seed_points m)) then failwith "wsfs: (457/500,2) not in seedPoints" else
  ignore concl; wsfs_original m 2 WSFS_LEFT_CENTER (`&1`, `&87 / &50`) (`&457 / &500`, `&2`) [8] 0;;

(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/WallReach.lean       *)
(* (namespace N12Compact.MergedPending; Lean header: "Source only,           *)
(* uncompiled").  Longer foreign bars for the three pending merged families. *)
(* Cases k : Case are the family constants MPF_FAMILIES = [c683; c700; c867];*)
(* per-case theorems are OCaml lists in that order.  owner p m is the tuple  *)
(* (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l; centerX / centerY = lcx /  *)
(* lcy.  pullSwap W = (s, c, u, --v - a, a); pullX / pullY: LINSIDE_PULLX /  *)
(* LINSIDE_PULLY.  ContinuousBottom.reach_of_far = C1089CB_REACH_OF_FAR,     *)
(* WallLowerCenterBarrier.center_above = WLCB_CENTER_ABOVE, WallSignChord.   *)
(* chord = WSC_CHORD; common_labels = MPD_COMMON_LABELS, singleton_* =       *)
(* MPSB_SINGLETON_*, c700_right_singleton = MPF_C700_RIGHT_SINGLETON,        *)
(* c700_right_labels / c867_right_labels / southeast_lower = MPD_*.          *)
(* The pulled geometric steps of top_reach / c700_right_reach /              *)
(* c867_right_upper are stated as local lemmas on an arbitrary square W.     *)
(* Tag MPWR_.                                                                *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_Domains.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_SingletonBars.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;

(* centerX (pullSwap W) = centerY W *)
let MPWR_LCX_PULLSW = prove
 (`forall c s u v a. lcx s c u (--v - a) a = lcy c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* centerY (pullX W) = centerY W *)
let MPWR_LCY_PULLX = prove
 (`forall c s u v a. lcy (--c) s (u - &4 * c) (--v - a - &4 * s) a = lcy c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REAL_ARITH_TAC);;

(* centers of pullY (pullX W) *)
let MPWR_CENTER_PULLYX = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcx (--c) (--s) ((u - &4 * c) - &4 * s) (&4 * --c - (--v - a - &4 * s) - a) a =
           &4 - lcx c s u v a /\
         lcy (--c) (--s) ((u - &4 * c) - &4 * s) (&4 * --c - (--v - a - &4 * s) - a) a =
           &4 - lcy c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  POP_ASSUM MP_TAC THEN CONV_TAC REAL_RING);;

let MPWR_PULL_TAC =
  CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[LCONT_PULLSW; LCONT_PULLX; LCONT_PULLY] THEN
    TRY(UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC);
    ALL_TAC];;

(* Lean: raw_left (private) *)
let MPWR_RAW_LEFT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&457 / &500) (&2) /\
     linside c s u v a (&1) (&12 / &5) /\
     ~linside c s u v a (&1) (&87 / &50) /\
     ~linside c s u v a (&19 / &25) (&187 / &100) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> &51 / &25 < lcy c s u v a /\ linside c s u v a (&1) (&14 / &5) /\
         forall y. &113 / &50 <= y /\ y <= &14 / &5 ==> linside c s u v a (&1) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`] C1089CB_REACH_OF_FAR) THEN
  REWRITE_TAC[LINSIDE_PULLSW; MPWR_LCX_PULLSW] THEN MPWR_PULL_TAC THEN DISCH_THEN ACCEPT_TAC);;

(* the pulled step of top_reach: reach_of_far on pullY (pullX W) (local) *)
let MPWR_RAW_TOP = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&2) (&1543 / &500) /\
     linside c s u v a (&8 / &5) (&3) /\
     ~linside c s u v a (&113 / &50) (&3) /\
     ~linside c s u v a (&213 / &100) (&81 / &25) /\
     ~linside c s u v a (&33 / &20) (&47 / &20)
     ==> lcx c s u v a < &49 / &25 /\
         forall x. &6 / &5 <= x /\ x <= &87 / &50 ==> linside c s u v a x (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--c`; `--s`; `(u - &4 * c) - &4 * s`; `&4 * --c - (--v - a - &4 * s) - a`;
                `a:real`] C1089CB_REACH_OF_FAR) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MPWR_CENTER_PULLYX th]) THEN REWRITE_TAC[LINSIDE_PULLY; LINSIDE_PULLX] THEN
  MPWR_PULL_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&4 - x`) THEN
  REWRITE_TAC[REAL_ARITH `&4 - (&4 - x) = x`] THEN DISCH_THEN MATCH_MP_TAC THEN
  RASM_ARITH_TAC);;

(* the pulled step of c700_right_reach: raw_left on pullY (pullX W) (local) *)
let MPWR_RAW_RIGHT = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&1543 / &500) (&2) /\
     linside c s u v a (&3) (&8 / &5) /\
     ~linside c s u v a (&3) (&113 / &50) /\
     ~linside c s u v a (&81 / &25) (&213 / &100) /\
     ~linside c s u v a (&47 / &20) (&33 / &20)
     ==> lcy c s u v a < &49 / &25 /\
         forall y. &6 / &5 <= y /\ y <= &87 / &50 ==> linside c s u v a (&3) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`--c`; `--s`; `(u - &4 * c) - &4 * s`; `&4 * --c - (--v - a - &4 * s) - a`;
                `a:real`] MPWR_RAW_LEFT) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MPWR_CENTER_PULLYX th]) THEN REWRITE_TAC[LINSIDE_PULLY; LINSIDE_PULLX] THEN
  MPWR_PULL_TAC THEN STRIP_TAC THEN CONJ_TAC THENL [RASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `&4 - y`) THEN
  REWRITE_TAC[REAL_ARITH `&4 - (&4 - y) = y`] THEN DISCH_THEN MATCH_MP_TAC THEN
  RASM_ARITH_TAC);;

(* the pulled steps of c867_right_upper: center_above and chord on pullX W (local) *)
let MPWR_RAW_C867 = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &1 < a /\ lcont c s u v a /\
     linside c s u v a (&1543 / &500) (&2) /\
     linside c s u v a (&3) (&12 / &5) /\
     ~linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&47 / &20) (&47 / &20)
     ==> &21 / &10 < lcy c s u v a /\
         forall y. &111 / &50 <= y /\ y <= &12 / &5 ==> linside c s u v a (&3) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&21 / &10 < lcy c s u v a` ASSUME_TAC THENL
   [MP_TAC(SPECL [`--c`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`] WLCB_CENTER_ABOVE) THEN
    REWRITE_TAC[LINSIDE_PULLX; MPWR_LCY_PULLX] THEN MPWR_PULL_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linside c s u v a (&3) (&111 / &50)` ASSUME_TAC THENL
   [MP_TAC(SPECL [`--c`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`; `&111 / &50`]
      WSC_CHORD) THEN
    REWRITE_TAC[LINSIDE_PULLX; MPWR_LCY_PULLX] THEN
    CONV_TAC(ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST
       [ASM_REWRITE_TAC[] THEN NO_TAC;
        UNDISCH_TAC `c * c + s * s = &1` THEN REAL_ARITH_TAC;
        REPEAT STRIP_TAC THEN UNDISCH_TAC `lcont c s u v a` THEN REWRITE_TAC[lcont] THEN
        DISCH_THEN(MP_TAC o SPECL [`&4 - x`; `y:real`]) THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        RASM_ARITH_TAC];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC OO_VERTICAL_SEGMENT THEN
  MAP_EVERY EXISTS_TAC [`&111 / &50`; `&12 / &5`] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ------------------------------------------------------------------------- *)
(* Packing level.                                                            *)
(* ------------------------------------------------------------------------- *)

let MPWR_VARS = MPD_FIVE;;
let mpwr_hyp fam = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam));;
let mpwr_np fam = CONJUNCT1 (ASSUME (mpwr_hyp fam));;
let mpwr_gen fam th = GENL MPWR_VARS (DISCH (mpwr_hyp fam) th);;
let mpwr_inst fam uth = MP (SPECL MPWR_VARS uth) (ASSUME (mpwr_hyp fam));;
let mpwr_tuple m =
  map (fun f -> list_mk_comb(f, MPWR_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let mpwr_seed fam m p = mpwr_inst fam (oo_inst fam (oo_seed m p));;
let mpwr_missing fam m k = mpwr_inst fam (oo_inst fam (oo_missing m k));;
let mpwr_auxpt m j mem = EQ_MP (SYM (SPECL (MPWR_VARS @ [mk_small_numeral m]) (oo_aux_point j))) mem;;
let mpwr_excl fam m n thn = mpwr_inst fam (oo_excl fam m n (mpwr_gen fam thn));;
(* common labels: [4,13 of 256; 1,11 of 4096; 6,15 of 8192; 3,14 of 32768] *)
let mpwr_labels fam =
  let i = index fam MPF_FAMILIES in
  CONJUNCTS (REWRITE_RULE[mpd_commonLabels] (mpwr_inst fam (el i MPD_COMMON_LABELS)));;
(* a point of a singleton bar  !t. lo <= t /\ t <= hi ==> linside .. *)
let mpwr_bar bar t =
  let th = SPEC t bar in MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th))));;
let mpwr_singleton fam lemma m t =
  let np = mpwr_np fam and img = CONJUNCT2 (ASSUME (mpwr_hyp fam)) in
  mpwr_bar (MP (SPECL (MPWR_VARS @ [fam]) lemma) (CONJ np (CONJ img (in_fam m fam)))) t;;

let mpwr_apply fam m lemma ths =
  let np = mpwr_np fam in
  let th = SPECL (mpwr_tuple m) lemma in
  let unit = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let box = MP (SPECL (MPWR_VARS @ [mk_small_numeral m]) OO_BOX) np in
  let side = MP (SPECL MPWR_VARS OO_SIDE) np in
  MP th (TAC_PROOF(([], lhand (concl th)),
    REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC ([unit; box; side] @ ths))));;

let mpwr_stmt fam body = list_mk_forall(MPWR_VARS, mk_imp(mpwr_hyp fam, body));;
let mpwr_prove fam body th =
  prove(mpwr_stmt fam body, REPEAT GEN_TAC THEN DISCH_TAC THEN ACCEPT_TAC th);;
let mpwr_inside m x y = list_mk_comb(`linside`, mpwr_tuple m @ [x; y]);;
let mpwr_center f m = list_mk_comb(f, mpwr_tuple m);;

(* Lean: left_reach *)
let MPWR_LEFT_REACH = map (fun fam ->
  let lab = mpwr_labels fam in
  let mark = mpwr_seed fam 4096 (`&457 / &500`, `&2`) in
  let far = mpwr_auxpt 4096 11 (el 3 lab) in
  let short = mpwr_singleton fam MPSB_SINGLETON_LEFT 2 `&87 / &50` in
  let extra = mpwr_seed fam 2 (`&19 / &25`, `&187 / &100`) in
  let central = mpwr_missing fam 4096 11 in
  let res = mpwr_apply fam 4096 MPWR_RAW_LEFT
    [mark; far; mpwr_excl fam 4096 2 short; mpwr_excl fam 4096 2 extra; central] in
  let y = `y:real` in
  mpwr_prove fam
    (mk_conj(mk_binop `(<):real->real->bool` `&51 / &25` (mpwr_center `lcy` 4096),
             mk_forall(y, mk_imp(`&113 / &50 <= y /\ y <= &14 / &5`, mpwr_inside 4096 `&1` y))))
    (CONJ (CONJUNCT1 res) (CONJUNCT2 (CONJUNCT2 res)))) MPF_FAMILIES;;

(* Lean: bottom_reach *)
let MPWR_BOTTOM_REACH = map (fun fam ->
  let lab = mpwr_labels fam in
  let mark = mpwr_seed fam 8192 (`&2`, `&457 / &500`) in
  let far = mpwr_auxpt 8192 6 (el 4 lab) in
  let short = mpwr_singleton fam MPSB_SINGLETON_BOTTOM 1 `&87 / &50` in
  let extra = mpwr_seed fam 1 (`&187 / &100`, `&19 / &25`) in
  let central = mpwr_missing fam 8192 9 in
  let res = mpwr_apply fam 8192 C1089CB_REACH_OF_FAR
    [mark; far; mpwr_excl fam 8192 1 short; mpwr_excl fam 8192 1 extra; central] in
  let x = `x:real` in
  mpwr_prove fam
    (mk_conj(mk_binop `(<):real->real->bool` `&51 / &25` (mpwr_center `lcx` 8192),
             mk_forall(x, mk_imp(`&113 / &50 <= x /\ x <= &14 / &5`, mpwr_inside 8192 x `&1`))))
    (CONJ (CONJUNCT1 res) (CONJUNCT2 (CONJUNCT2 res)))) MPF_FAMILIES;;

(* Lean: top_reach *)
let MPWR_TOP_REACH = map (fun fam ->
  let lab = mpwr_labels fam in
  let mark = mpwr_seed fam 32768 (`&2`, `&1543 / &500`) in
  let far = mpwr_auxpt 32768 3 (el 6 lab) in
  let short = mpwr_singleton fam MPSB_SINGLETON_TOP 16 `&113 / &50` in
  let extra = mpwr_seed fam 16 (`&213 / &100`, `&81 / &25`) in
  let central = mpwr_missing fam 32768 11 in
  let res = mpwr_apply fam 32768 MPWR_RAW_TOP
    [mark; far; mpwr_excl fam 32768 16 short; mpwr_excl fam 32768 16 extra; central] in
  let x = `x:real` in
  mpwr_prove fam
    (mk_conj(mk_binop `(<):real->real->bool` (mpwr_center `lcx` 32768) `&49 / &25`,
             mk_forall(x, mk_imp(`&6 / &5 <= x /\ x <= &87 / &50`, mpwr_inside 32768 x `&3`))))
    res) MPF_FAMILIES;;

(* Lean: c700_right_reach *)
let MPWR_C700_RIGHT_REACH =
  let fam = `mpf_family_c700` in
  let mark = mpwr_seed fam 16384 (`&1543 / &500`, `&2`) in
  let far = mpwr_auxpt 16384 18 (CONJUNCT2 (mpwr_inst fam MPD_C700_RIGHT_LABELS)) in
  let short = mpwr_bar (mpwr_inst fam MPF_C700_RIGHT_SINGLETON) `&113 / &50` in
  let extra = mpwr_seed fam 32 (`&81 / &25`, `&213 / &100`) in
  let central = mpwr_missing fam 16384 9 in
  let res = mpwr_apply fam 16384 MPWR_RAW_RIGHT
    [mark; far; mpwr_excl fam 16384 32 short; mpwr_excl fam 16384 32 extra; central] in
  let y = `y:real` in
  mpwr_prove fam
    (mk_conj(mk_binop `(<):real->real->bool` (mpwr_center `lcy` 16384) `&49 / &25`,
             mk_forall(y, mk_imp(`&6 / &5 <= y /\ y <= &87 / &50`, mpwr_inside 16384 `&3` y))))
    res;;

(* Lean: c867_right_upper *)
let MPWR_C867_RIGHT_UPPER =
  let fam = `mpf_family_c867` in
  let mark = mpwr_seed fam 16384 (`&1543 / &500`, `&2`) in
  let far = mpwr_auxpt 16384 19 (CONJUNCT2 (mpwr_inst fam MPD_C867_RIGHT_LABELS)) in
  let lower = mpwr_auxpt 512 8
    (MP (SPECL MPWR_VARS (el 2 MPD_SOUTHEAST_LOWER))
        (CONJ (mpwr_np fam) (CONJ (CONJUNCT2 (ASSUME (mpwr_hyp fam))) (in_fam 512 fam)))) in
  let central = mpwr_missing fam 16384 10 in
  let res = mpwr_apply fam 16384 MPWR_RAW_C867
    [mark; far; mpwr_excl fam 16384 512 lower; central] in
  let y = `y:real` in
  mpwr_prove fam
    (mk_conj(mk_binop `(<):real->real->bool` `&21 / &10` (mpwr_center `lcy` 16384),
             mk_forall(y, mk_imp(`&111 / &50 <= y /\ y <= &12 / &5`, mpwr_inside 16384 `&3` y))))
    res;;

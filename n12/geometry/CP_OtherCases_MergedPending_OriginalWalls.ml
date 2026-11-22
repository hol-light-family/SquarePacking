(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/MergedPending/OriginalWalls.lean    *)
(* (namespace N12Compact.MergedPending).  Literal original-owner wall cuts. *)
(* owner p m is (ooc .. m) (oos .. m) (oou .. m) (oov .. m) l; centerX /    *)
(* centerY are lcx / lcy; Lean pullY (pullX W) (the half-turn) is the       *)
(* square (--c, --s, u - 4c - 4s, v + 4s - 4c, a) (MPOW_HALF).              *)
(* WallSignFromSingleton.left_chord / bottom_chord / original_bottom:       *)
(* WSFS_LEFT_CHORD / WSFS_BOTTOM_CHORD / wsfs_original_bottom;              *)
(* SingletonBars: MPSB_SINGLETON_*.                                         *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_SingletonBars.ml";;
needs "n12/geometry/CP_CommonCases_WallSignFromSingleton.ml";;

let MPOW_HALF = prove
 (`forall c s u v a x y.
     linside (--c) (--s) (u - &4 * c - &4 * s) (v + &4 * s - &4 * c) a x y <=>
     linside c s u v a (&4 - x) (&4 - y)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let MPOW_HALF_CENTRE = prove
 (`forall c s u v a. c * c + s * s = &1
     ==> lcx (--c) (--s) (u - &4 * c - &4 * s) (v + &4 * s - &4 * c) a = &4 - lcx c s u v a /\
         lcy (--c) (--s) (u - &4 * c - &4 * s) (v + &4 * s - &4 * c) a = &4 - lcy c s u v a`,
  REWRITE_TAC[lcx; lcy] THEN REPEAT GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THEN
  UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING);;

let mpow_owner m f = list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`;
                                     `b:num->real`; `l:real`; mk_small_numeral m]);;

(* assumptions about owner m: unit, side, box, a seed, missing markers, and the
   point (fx, fy) of the foreign owner n excluded from m; then abbreviate owner m *)
let MPOW_SETUP_TAC m n seed misses foreign =
  let five = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`] in
  MP_TAC(SPECL (five @ [mk_small_numeral m]) OO_UNIT) THEN
  MP_TAC(SPECL five OO_SIDE) THEN
  MP_TAC(SPECL (five @ [mk_small_numeral m]) OO_BOX) THEN
  MP_TAC(SPECL OO_VARS (oo_seed m seed)) THEN
  MAP_EVERY (fun k -> MP_TAC(SPECL OO_VARS (oo_missing m k))) misses THEN
  MP_TAC(SPECL OO_VARS (oo_seed n foreign)) THEN
  MP_TAC(SPECL (OO_VARS @ [mk_small_numeral m; mk_small_numeral n]) OO_APART) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[ldisj; lcont] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN (mk_neg(list_mk_comb(`linside`, map (mpow_owner m) [`ooc`; `oos`; `oou`; `oov`] @
                  [`l:real`; fst foreign; snd foreign])))
    ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC (mk_eq(`C:real`, mpow_owner m `ooc`)) THEN
  ABBREV_TAC (mk_eq(`S:real`, mpow_owner m `oos`)) THEN
  ABBREV_TAC (mk_eq(`U:real`, mpow_owner m `oou`)) THEN
  ABBREV_TAC (mk_eq(`V:real`, mpow_owner m `oov`));;

(* Lean: left_wall *)
let MPOW_LEFT_WALL = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     4096 IN fam /\ 2 IN fam
     ==> &2 < lcy (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096)
                  (oov c1 c2 a b l 4096) l /\
         forall y. &111 / &50 <= y /\ y <= &239 / &100
             ==> linside (ooc c1 c2 a b l 4096) (oos c1 c2 a b l 4096) (oou c1 c2 a b l 4096)
                         (oov c1 c2 a b l 4096) l (&1) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MPOW_SETUP_TAC 4096 2 (`&457 / &500`, `&2`) [8; 11] (`&1`, `&87 / &50`) THEN
  MATCH_MP_TAC WSFS_LEFT_CHORD THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* Lean: bottom_wall *)
let MPOW_BOTTOM_WALL = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     8192 IN fam /\ 1 IN fam
     ==> &2 < lcx (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
                  (oov c1 c2 a b l 8192) l /\
         forall x. &111 / &50 <= x /\ x <= &239 / &100
             ==> linside (ooc c1 c2 a b l 8192) (oos c1 c2 a b l 8192) (oou c1 c2 a b l 8192)
                         (oov c1 c2 a b l 8192) l x (&1)`,
  ACCEPT_TAC(wsfs_original_bottom 8192));;

(* Lean: top_wall *)
let MPOW_TOP_WALL = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     32768 IN fam /\ 16 IN fam
     ==> lcx (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
             (oov c1 c2 a b l 32768) l < &2 /\
         forall x. &161 / &100 <= x /\ x <= &89 / &50
             ==> linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
                         (oov c1 c2 a b l 32768) l x (&3)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MPOW_SETUP_TAC 32768 16 (`&2`, `&1543 / &500`) [10; 11] (`&113 / &50`, `&3`) THEN
  MP_TAC(SPECL [`--C`; `--S`; `U - &4 * C - &4 * S`; `V + &4 * S - &4 * C`; `l:real`]
    WSFS_BOTTOM_CHORD) THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `U:real`; `V:real`; `l:real`] MPOW_HALF_CENTRE) THEN
  ASM_REWRITE_TAC[MPOW_HALF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`&4 - x`; `&4 - y`] o
        check (fun th -> is_forall(concl th) &&
          can (term_match [] `forall x y. linside c s u v a x y ==> P x y`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&4 - x` o check (is_forall o concl)) THEN
  REWRITE_TAC[REAL_ARITH `&4 - (&4 - x) = x`] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* Lean: right_wall *)
let MPOW_RIGHT_WALL = prove
 (`forall c1 c2 a b l fam. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     16384 IN fam /\ 32 IN fam
     ==> lcy (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384)
             (oov c1 c2 a b l 16384) l < &2 /\
         forall y. &161 / &100 <= y /\ y <= &89 / &50
             ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384)
                         (oov c1 c2 a b l 16384) l (&3) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MPOW_SETUP_TAC 16384 32 (`&1543 / &500`, `&2`) [10; 9] (`&3`, `&113 / &50`) THEN
  MP_TAC(SPECL [`--C`; `--S`; `U - &4 * C - &4 * S`; `V + &4 * S - &4 * C`; `l:real`]
    WSFS_LEFT_CHORD) THEN
  MP_TAC(SPECL [`C:real`; `S:real`; `U:real`; `V:real`; `l:real`] MPOW_HALF_CENTRE) THEN
  ASM_REWRITE_TAC[MPOW_HALF] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`&4 - x`; `&4 - y`] o
        check (fun th -> is_forall(concl th) &&
          can (term_match [] `forall x y. linside c s u v a x y ==> P x y`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&4 - y` o check (is_forall o concl)) THEN
  REWRITE_TAC[REAL_ARITH `&4 - (&4 - y) = y`] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

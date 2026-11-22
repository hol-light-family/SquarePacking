(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperCenter.lean (N12Compact.C868).            *)
(* The nonnegative upper-central sector has an actual strict centre (2,2).   *)
(* Lean antidiagonal q = pullSwap (pullX (pullY q)) and turnFrame are        *)
(* parameter transforms (c868_pull with LINSIDE_PULLSW/X/Y, C868UC_TURN);    *)
(* inside_antidiagonal is the rewriting C868UC_RULE.  MergedLeftNegative.     *)
(* point = MLN_POINT, SingletonMissing.one_missing_points =                  *)
(* CCSM_ONE_MISSING_POINTS (ExactMarkers from OO_MARKERS).  Tag C868UC_.     *)
(* ========================================================================= *)

needs "n12/geometry/ActualCrosspoints.ml";;
needs "n12/geometry/NegativeCornerSector.ml";;
needs "n12/geometry/MergedLeftNegative.ml";;
needs "n12/geometry/CP_CommonCases_SingletonMissing.ml";;

(* Lean: turnFrame_inside *)
let C868UC_TURN = prove
 (`forall c s u v a x y. linside (--s) c v (--u - a) a x y <=> linside c s u v a x y`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

let c868uc_turn = c868_pull C868UC_TURN;;
(* Lean: antidiagonal (private) *)
let c868uc_anti sq = c868_pullsw (c868_pullx (c868_pully sq));;
let C868UC_SQ = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`];;
(* Lean: inside_antidiagonal (private) *)
let C868UC_INSIDE_ANTIDIAGONAL = prove
 (list_mk_forall(C868UC_SQ @ [`x:real`; `y:real`],
    mk_iff(list_mk_comb(`linside`, c868uc_anti C868UC_SQ @ [`x:real`; `y:real`]),
           `linside c s u v a (&4 - y) (&4 - x)`)),
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
(* Lean: ai (local) *)
let C868UC_INSIDE_TURNED = prove
 (list_mk_forall(C868UC_SQ @ [`x:real`; `y:real`],
    mk_iff(list_mk_comb(`linside`, c868uc_turn (c868uc_anti C868UC_SQ) @ [`x:real`; `y:real`]),
           `linside c s u v a (&4 - y) (&4 - x)`)),
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;
let C868UC_RULE = CONV_RULE (ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV) o
  REWRITE_RULE[C868UC_INSIDE_TURNED; C868UC_INSIDE_ANTIDIAGONAL];;

let C868UC_IH = `forall x y. linside cH sH uH vH aH x y <=>
                   linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                           (oov c1 c2 a b l 3072) l x y`;;

(* Lean: upper_nonnegative_center *)
let C868UC_UPPER_NONNEGATIVE_CENTER = c868_check
 `forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     &0 < cH /\ &0 <= sH /\ sH <= cH /\ aH = l /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> linside cH sH uH vH aH (&2) (&2)`
 (let sqh = C868PS_SQ_H in
  let hs = [`cH * cH + sH * sH = &1`; `&0 < aH`; `&0 < cH`; `&0 <= sH`; `sH <= cH`; `aH:real = l`; C868UC_IH] in
  let ih = ASSUME C868UC_IH in
  let sh = ASSUME `aH:real = l` in
  let sqa = c868uc_turn (c868uc_anti sqh) in
  let sql = c868uc_anti (c868_own 32768) in
  let lemma = C868UC_RULE (SPECL (sqa @ sql) MLN_POINT) in
  let box = MATCH_MP LCONT_PULLSW (MATCH_MP LCONT_PULLX (MATCH_MP LCONT_PULLY (c868_box 32768))) in
  let hf = map (c868_to ih)
    [c868_seed_f 3072 (`&47 / &20`, `&47 / &20`); c868_seed_f 3072 (`&33 / &20`, `&47 / &20`);
     c868_excl_f 3072 16 (c868_mp C868AO_ADDITIONAL_INSIDE.(1));
     c868_excl_f 3072 32768 (c868_forced_f 2);
     c868_excl_f 3072 4096 (c868_mp C868AO_ADDITIONAL_INSIDE.(3))] in
  let lf = [c868_seed_f 32768 (`&2`, `&1543 / &500`); c868_mp C868AO_ADDITIONAL_INSIDE.(6)] in
  let ap = REWRITE_RULE[ldisj] (c868_apart_f 3072 32768) in
  let dterm = list_mk_comb(`ldisj`, sqa @ sql) in
  let dis = c868_prove [ih; ap] dterm
     (REWRITE_TAC[ldisj; C868UC_INSIDE_TURNED; C868UC_INSIDE_ANTIDIAGONAL] THEN
      ASM_REWRITE_TAC[]) in
  let base = map ASSUME (butlast hs) @ [C868_SIDE] in
  let res = c868_discharge (hf @ lf @ [box; dis] @ base) lemma in
  c868_genx sqh hs res);;

(* Lean: nonnegative_upper_residue *)
let C868UC_NONNEGATIVE_UPPER_RESIDUE = prove
 (`forall c1 c2 a b l cA sA uA vA aA cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cA * cA + sA * sA = &1 /\ &0 < aA /\ cH * cH + sH * sH = &1 /\ &0 < aH /\
     &0 < cA /\ abs sA <= cA /\ &0 < cH /\ &0 <= sH /\ sH <= cH /\ aA = l /\ aH = l /\
     (forall x y. linside cA sA uA vA aA x y <=>
            linside (ooc c1 c2 a b l 256) (oos c1 c2 a b l 256) (oou c1 c2 a b l 256)
                    (oov c1 c2 a b l 256) l x y) /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> sA < &0 /\
         linside (ooc c1 c2 a b l 1) (oos c1 c2 a b l 1) (oou c1 c2 a b l 1) (oov c1 c2 a b l 1) l (&1) (&1) /\
         linside cH sH uH vH aH (&2) (&2) /\
         vA + aA <= &2 * (cA - sA) /\
         linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l
                 (&1) (&91 / &50) /\
         linside (ooc c1 c2 a b l 2) (oos c1 c2 a b l 2) (oou c1 c2 a b l 2) (oov c1 c2 a b l 2) l
                 (&19 / &25) (&49 / &25)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `sA < &0` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC (SPECL (C868OW_VARS @ C868PS_SQ_A @ C868PS_SQ_H) C868PS_POSITIVE_FRAMES_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN (list_mk_comb(`linside`, c868_own 1 @ [`&1`; `&1`])) ASSUME_TAC THENL
   [MATCH_MP_TAC (TAUT `(~p ==> false) ==> p`) THEN DISCH_TAC THEN
    MP_TAC (SPECL (C868OW_VARS @ C868PS_SQ_A @ C868PS_SQ_H) C868NC_NEGATIVE_CORNER_FRAMES_IMPOSSIBLE) THEN
    ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN
    REPEAT CONJ_TAC THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `linside cH sH uH vH aH (&2) (&2)` ASSUME_TAC THENL
   [MATCH_MP_TAC (SPECL (C868OW_VARS @ C868PS_SQ_H) C868UC_UPPER_NONNEGATIVE_CENTER) THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [(* height *)
    SUBGOAL_THEN `~linside cA sA uA vA aA (&2) (&2)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC (SPECL [`&2`; `&2`] (REWRITE_RULE[ldisj] (UNDISCH (SPECL C868OW_VARS (c868_apart 256 3072))))) THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC (UNDISCH (SPECL C868OW_VARS (c868_seed 256 (`&33 / &20`, `&33 / &20`)))) THEN
    MP_TAC (CONJUNCT2 (UNDISCH (SPECL C868OW_VARS C868AC_SOUTHWEST_CROSSPOINTS))) THEN
    FIRST_X_ASSUM (fun th -> if can (find_term ((=) `cA:real`)) (concl th) && is_forall (concl th)
                             then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[linside] THEN
    UNDISCH_TAC `aA:real = l` THEN
    UNDISCH_TAC `abs sA <= cA` THEN UNDISCH_TAC `&0 < cA` THEN UNDISCH_TAC `sA < &0` THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* stronger singleton points of owner 2 *)
  MP_TAC (SPECL (c868_own 2) CCSM_ONE_MISSING_POINTS) THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[OO_UNIT];
    ASM_MESON_TAC[OO_SIDE; REAL_ARITH `&1 < l ==> &0 < l`];
    ASM_MESON_TAC[OO_SIDE];
    ASM_MESON_TAC[OO_SIDE_LE];
    ASM_MESON_TAC[OO_BOX];
    MP_TAC (SPECL (C868OW_VARS @ [C868OW_F; `2`]) OO_MARKERS) THEN
    ASM_REWRITE_TAC[in_fam 2 C868OW_F; bitset_bits 2; IN_SET_OF_LIST; MEM];
    DISCH_TAC THEN
    MP_TAC (SPECL [`&1`; `&1`] (REWRITE_RULE[ldisj] (UNDISCH (SPECL C868OW_VARS (c868_apart 1 2))))) THEN
    ASM_REWRITE_TAC[]]);;

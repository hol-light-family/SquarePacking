(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/OriginalEntrance.lean        *)
(* (namespace N12Compact.Completion.OtherCases.C1090.OriginalData; Lean      *)
(* header: "All new source remains uncompiled").  The complete actual-family *)
(* producer of C1090's AuxiliaryEntrance (owners p) (= c1090od_auxent of the *)
(* owner coordinate functions c1090od_owners), and with it the exclusion of  *)
(* the C1090 family / case 1090 / original row 574.                          *)
(* owners p i = owner (EL i c1090od_masks): 0 -> 1, 4 -> 256, 5 -> 512,       *)
(* 8 -> 4098, 9 -> 8192, 10 -> 16384.  owner_apart = oo_apart.  Tag C1090OEN_.*)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1090_DirectDomains.ml";;
needs "n12/geometry/CP_OtherCases_C1090_RowIdentity.ml";;
needs "n12/geometry/CP_OtherCases_C1090_MergedLeftSeed.ml";;
needs "n12/geometry/CP_CommonCases_WallSignFromSingleton.ml";;

let C1090OEN_HYP = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1090od_family`;;

(* Lean: auxiliary_entrance *)
let C1090OEN_AUXILIARY_ENTRANCE =
  let vars = C1090AV_VARS and fam = C1090OD_F in
  let h = ASSUME C1090OEN_HYP in
  let hnp = CONJUNCT1 h in
  let use th = CONV_RULE C1090OD_EL_CONV (MP (SPECL vars th) h) in
  let apart m n = use (oo_apart fam m n) in
  (* a point of owner m (thm a) also in owner n (thm from other) contradicts apart m n *)
  let kill m n other a =
    let args = snd (strip_comb (concl a)) in
    let x = el 5 args and y = el 6 args in
    let d = SPECL [x; y] (REWRITE_RULE[ldisj] (apart m n)) in
    MP (NOT_ELIM d) (CONJ a (other x y)) in
  let fixed th _ _ = th in
  (* d1 \/ ... \/ dn with killers for d1 .. d(n-1) gives dn *)
  let rec elim th ks = match ks with
      [] -> th
    | k :: rest ->
        let d1, r = dest_disj (concl th) in
        let rr = elim (ASSUME r) rest in
        DISJ_CASES th (CONTR (concl rr) (k (ASSUME d1))) rr in
  let near = use (c1090od_seed 0 (`&28 / &25`, `&1`)) in
  let far = use (c1090od_seed 0 (`&87 / &50`, `&1`)) in
  let singletonF2 = MATCH_MP OO_HORIZONTAL_SEGMENT
    (end_itlist CONJ [near; far; REAL_RAT_REDUCE_CONV `&28 / &25 < &87 / &50` |> EQT_ELIM;
       EQT_ELIM (REAL_RAT_REDUCE_CONV `&28 / &25 <= &8 / &5`);
       EQT_ELIM (REAL_RAT_REDUCE_CONV `&8 / &5 <= &87 / &50`)]) in
  let leftMarker = use (c1090od_seed 8 (`&457 / &500`, `&2`)) in
  let side = MP (SPECL vars OO_SIDE) hnp in
  let unit8 = MP (SPECL (vars @ [`4098`]) OO_UNIT) hnp in
  let box8 = MP (SPECL (vars @ [`4098`]) OO_BOX) hnp in
  let leftBar = MATCH_MP C1090MLS_ACTUAL_SEGMENT
    (end_itlist CONJ [unit8; MATCH_MP (REAL_ARITH `&1 < l ==> &0 < l`) side; side; box8;
                      use C1090OD_MARKER1_OWNED; leftMarker]) in
  let bar _ y =
    let s = SPEC y leftBar in
    let s = MP s (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl s)))) in
    MP s (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl s)))) in
  let southwestF4 = elim (use C1090AV_SOUTHWEST_F_COVER)
    [kill 256 4098 bar; kill 256 1 (fixed singletonF2)] in
  let southwestG3 = elim (use C1090AV_SOUTHWEST_G_COVER)
    [kill 256 4098 bar; kill 256 1 (fixed far)] in
  let bottomF6 = elim (use C1090AV_BOTTOM_F_COVER)
    [kill 8192 1 (fixed singletonF2); kill 8192 256 (fixed southwestF4)] in
  let southeastF8 = elim (use C1090AV_SOUTHEAST_F_COVER)
    [kill 512 256 (fixed southwestF4); kill 512 8192 (fixed bottomF6)] in
  let bottomChord =
    let th = SPEC fam (SPECL vars (wsfs_original_bottom 8192)) in
    CONJUNCT2 (MP th (end_itlist CONJ [hnp; CONJUNCT2 h; in_fam 8192 fam; in_fam 1 fam])) in
  let bottomG5 =
    let s = SPEC `&113 / &50` bottomChord in
    MP s (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl s)))) in
  let rightMissing =
    let mem = `8 IN ooaux c1 c2 a b l 16384` in
    let pt = EQ_MP (SYM (SPECL (vars @ [`16384`]) (oo_aux_point 8))) (ASSUME mem) in
    NOT_INTRO (DISCH mem (kill 16384 512 (fixed southeastF8) pt)) in
  let rightPair = MP (SPECL vars C1090DD_RIGHT_POINTS) (CONJ hnp (CONJ (CONJUNCT2 h) rightMissing)) in
  let facts = [southwestF4; southwestG3; southeastF8; bottomF6; bottomG5;
               CONJUNCT1 rightPair; CONJUNCT2 rightPair;
               use C1090AV_SOUTHEAST_G_COVER; use C1090AV_NORTHEAST_F_COVER;
               use C1090AV_NORTHEAST_G_COVER; use C1090AV_NORTHWEST_F_COVER;
               use C1090AV_NORTHWEST_G_COVER; use C1090DD_TOP_COMPONENT] in
  prove(C1090RID_PRODUCE,
    REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[c1090od_auxent] THEN BETA_TAC THEN
    CONV_TAC C1090OD_EL_CONV THEN REPEAT CONJ_TAC THEN FIRST (map ACCEPT_TAC facts));;

(* Lean: family_excluded *)
let C1090OEN_FAMILY_EXCLUDED =
  MP C1090RID_FAMILY_EXCLUDED_OF_AUXILIARY_ENTRANCE C1090OEN_AUXILIARY_ENTRANCE;;

(* Lean: case_excluded *)
let C1090OEN_CASE_EXCLUDED =
  MP C1090RID_CASE_EXCLUDED_OF_AUXILIARY_ENTRANCE C1090OEN_AUXILIARY_ENTRANCE;;

(* whole-case closer: original row 574 (case 1090) *)
let C1090OEN_EXCLUDED_ROW = ri_excluded_row 574 C1090OEN_CASE_EXCLUDED;;

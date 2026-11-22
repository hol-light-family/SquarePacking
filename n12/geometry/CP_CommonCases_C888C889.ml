(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C888C889.lean                      *)
(* (N12Compact.CommonCases.C888C889).  Complete original C888 (b = false,    *)
(* family c888d_family_f, rightMask 16384) and C889 (b = true,               *)
(* c888d_family_t, rightMask 16416) endings from the shared entrance         *)
(* (C888E_ENTRANCE_F/_T).  Statements for the Lean parameter b are the two   *)
(* theorems _F and _T.  seed_point = C888E_SEED_POINT, auxiliary_point /     *)
(* auxiliary_exact = oo_aux_point, missing_marker = oo_missing,              *)
(* horizontal_segment = OO_HORIZONTAL_SEGMENT; C981CompletionWallAdvance.    *)
(* point = C981WA_POINT, C1092MixedSpan.impossible = C1092MS_IMPOSSIBLE,      *)
(* InwardPoint.point_original = CCIP_POINT_ORIGINAL, StrongBarPoint.         *)
(* point_original = CCSBP_POINT_ORIGINAL, CentralPair.impossible =           *)
(* CCCPAIR_IMPOSSIBLE; pullY / pullSwap via LINSIDE_PULLY / LINSIDE_PULLSW.  *)
(* Rows 475 (C888) and 476 (C889) via RowIdentity.  Tag CCC888_.             *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_C888C889Entrance.ml";;
needs "n12/geometry/CP_CommonCases_CentralPair.ml";;
needs "n12/geometry/CP_CommonCases_StrongBarPoint.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/RowIdentity.ml";;

let CCC888_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

let ccc888_q m = map (fun f -> list_mk_comb(f, CCC888_VARS @ [mk_small_numeral m]))
                   [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let ccc888_pull tms q =
  match q with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms
  | _ -> failwith "ccc888_pull";;
let ccc888_pully = ccc888_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let ccc888_pullsw = ccc888_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* side conditions of a lemma instance: facts, unit normals of pulled squares, ldisj of pulled pairs *)
let CCC888_DISCH_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
         (FIRST_ASSUM ACCEPT_TAC ORELSE (ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC));
         REWRITE_TAC[ldisj; LINSIDE_PULLY; LINSIDE_PULLSW] THEN REPEAT GEN_TAC THEN
         FIRST_ASSUM MATCH_ACCEPT_TAC];;

(* apply a geometry lemma to (possibly pulled) owners; antecedents from facts *)
let ccc888_app th tup facts =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLY; LINSIDE_PULLSW] THENC REAL_RAT_REDUCE_CONV)
              (SPECL tup th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  let ant = lhand (concl th') in
  MP th' (TAC_PROOF((map (fun t -> ("", t)) facts, ant), REPEAT CONJ_TAC THEN CCC888_DISCH_TAC));;

(* |- j IN S  or  |- ~(j IN S)  from |- S = literal *)
let ccc888_mem_eq eqth j =
  let t = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j), lhs (concl eqth)) in
  let r = REWRITE_CONV[eqth; IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] t in
  if rand (concl r) = `true` then EQT_ELIM r else EQF_ELIM r;;

(* |- j IN S from |- {..} SUBSET S *)
let ccc888_mem_sub sub j =
  find (fun th -> lhand (concl th) = mk_small_numeral j)
    (CONJUNCTS (REWRITE_RULE[INSERT_SUBSET; EMPTY_SUBSET] sub));;

let ccc888_family_impossible b =
  let fam = c888e_fam b in
  let rm = if b then 16416 else 16384 in
  let hyp = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)) in
  let hh = ASSUME hyp in
  let np = CONJUNCT1 hh in
  let mp th = MP (SPECL CCC888_VARS th) hh in
  let seed m p = mp (C888E_SEED_POINT b m p) in
  let apart m n = REWRITE_RULE[ldisj] (mp (oo_apart fam m n)) in
  let foreign m n thn =
    let args = snd (strip_comb (concl thn)) in
    let d = SPECL [el 5 args; el 6 args] (apart m n) in
    let a = lhand (rand (concl d)) in
    NOT_INTRO (DISCH a (MP (NOT_ELIM d) (CONJ (ASSUME a) thn))) in
  let unit m = MP (SPECL (CCC888_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let box m = MP (SPECL (CCC888_VARS @ [mk_small_numeral m]) OO_BOX) np in
  let side = MP (SPECL CCC888_VARS OO_SIDE) np in
  let side0 = MP (REAL_ARITH `&1 < l ==> &0 < l`) side in
  let pt m j memth = EQ_MP (SYM (SPECL (CCC888_VARS @ [mk_small_numeral m]) (oo_aux_point j))) memth in
  let nopt m j nmemth =
    EQ_MP (SYM (AP_TERM `(~)` (SPECL (CCC888_VARS @ [mk_small_numeral m]) (oo_aux_point j)))) nmemth in
  let hseg th0 th1 x0 x1 =
    (* !z. x0 <= z /\ z <= x1 ==> owner z y *)
    let args = snd (strip_comb (concl th0)) in
    let z = `z:real` in
    let lo = mk_binop `(<=):real->real->bool` x0 z and hi = mk_binop `(<=):real->real->bool` z x1 in
    let lt = REAL_ARITH (mk_binop `(<):real->real->bool` (el 5 args) x1) in
    let seg = MP (SPECL (fst (chop_list 5 args) @ [el 5 args; x1; el 6 args; z]) OO_HORIZONTAL_SEGMENT)
                 (end_itlist CONJ [th0; th1; lt; CONJUNCT1 (ASSUME (mk_conj(lo, hi)));
                                   CONJUNCT2 (ASSUME (mk_conj(lo, hi)))]) in
    GEN z (DISCH (mk_conj(lo, hi)) seg) in
  let entrance = mp (if b then C888E_ENTRANCE_T else C888E_ENTRANCE_F) in
  let bottomAux = CONJUNCT1 entrance in
  let pattern = REWRITE_RULE[c888e_pattern] (CONJUNCT2 entrance) in
  (* Lean: markA .. seMarker *)
  let markA = seed 512 (`&47 / &20`, `&33 / &20`) in
  let markN = seed 1024 (`&47 / &20`, `&47 / &20`) in
  let markSW = seed 2304 (`&33 / &20`, `&33 / &20`) in
  let markNW = seed 2304 (`&33 / &20`, `&47 / &20`) in
  let markR = seed rm (`&1543 / &500`, `&2`) in
  let bottomMarker = seed 8192 (`&2`, `&457 / &500`) in
  let bottomElbow = pt 8192 15 (ccc888_mem_sub bottomAux 15) in
  let bottomOuter = pt 8192 6 (ccc888_mem_sub bottomAux 6) in
  let swTip = seed 1 (`&87 / &50`, `&1`) in
  let swSeed = seed 1 (`&187 / &100`, `&19 / &25`) in
  let topElbow = seed 16 (`&113 / &50`, `&3`) in
  let topTip = seed 16 (`&72 / &25`, `&3`) in
  let topSegment = hseg topElbow topTip `&113 / &50` `&72 / &25` in
  let seCorner = seed 12 (`&3`, `&1`) in
  let seMarker = seed 12 (`&1543 / &500`, `&1`) in
  let top_foreign m th =
    let z = `z:real` in
    let a = lhand (snd (dest_forall (concl th))) in
    let p = MP (SPEC z th) (ASSUME a) in
    GEN z (DISCH a (foreign m 16 p)) in
  (* Lean: bottomAdvance *)
  let bottomAdvance =
    ccc888_app C981WA_POINT (ccc888_pullsw (ccc888_q 8192))
      [unit 8192; side; side0; MATCH_MP LCONT_PULLSW (box 8192); bottomMarker; bottomOuter;
       foreign 8192 1 swTip; foreign 8192 1 swSeed; foreign 8192 512 markA] in
  let bottomSegment = hseg bottomElbow bottomAdvance `&113 / &50` `&14 / &5` in
  let top12 = MP (SPEC `&12 / &5` topSegment) (REAL_ARITH `&113 / &50 <= &12 / &5 /\ &12 / &5 <= &72 / &25`) in
  let lp, up = dest_disj (concl pattern) in
  (* --- lower pattern --- *)
  let lower =
    let lh = ASSUME lp in
    let aPair = CONJUNCT1 lh and nOptions = REWRITE_RULE[MEM] (CONJUNCT2 lh) in
    let inwardA = pt 512 4 (ccc888_mem_sub aPair 4) in
    let elbowA = pt 512 16 (ccc888_mem_sub aPair 16) in
    let missingG = foreign 1024 512 elbowA in
    let n1, nr = dest_disj (concl nOptions) in
    let n2, n3 = dest_disj nr in
    let nUpper e = pt 1024 19 (ccc888_mem_eq e 19) in
    let mixed =
      let e = ASSUME n1 in
      ccc888_app C1092MS_IMPOSSIBLE (ccc888_pully (ccc888_q 1024))
        [unit 1024; side; side0; pt 1024 5 (ccc888_mem_eq e 5); nUpper e; missingG;
         nopt 1024 9 (ccc888_mem_eq e 9); foreign 1024 16 topElbow; foreign 1024 16 top12] in
    let outward n =
      let e = ASSUME n in
      let nOutward = pt 1024 9 (ccc888_mem_eq e 9) in
      let inwardPoint =
        ccc888_app CCIP_POINT_ORIGINAL (ccc888_q 512)
          [unit 512; side; markA; inwardA; elbowA; foreign 512 2304 markSW;
           foreign 512 1024 markN; foreign 512 8192 bottomOuter] in
      let missingH = mp (oo_inst fam (oo_missing 1024 5)) in
      let avoid = top_foreign 1024
        (GEN `z:real` (DISCH `&113 / &50 <= z /\ z <= &143 / &50`
           (MP (SPEC `z:real` topSegment)
               (MP (REAL_ARITH `&113 / &50 <= z /\ z <= &143 / &50 ==> &113 / &50 <= z /\ z <= &72 / &25`)
                   (ASSUME `&113 / &50 <= z /\ z <= &143 / &50`))))) in
      let outwardPoint =
        ccc888_app CCSBP_POINT_ORIGINAL (ccc888_q 1024)
          [unit 1024; side; side0; markN; nOutward; nUpper e; missingG; foreign 1024 rm markR;
           missingH; avoid] in
      MP (NOT_ELIM (SPECL [`&123 / &50`; `&199 / &100`] (apart 512 1024))) (CONJ inwardPoint outwardPoint) in
    DISJ_CASES nOptions mixed (DISJ_CASES (ASSUME nr) (outward n2) (outward n3)) in
  (* --- upper pattern --- *)
  let upper =
    let uh = ASSUME up in
    let nPair = CONJUNCT1 uh and aOptions = REWRITE_RULE[MEM] (CONJUNCT2 uh) in
    let inwardN = pt 1024 5 (ccc888_mem_sub nPair 5) in
    let elbowN = pt 1024 16 (ccc888_mem_sub nPair 16) in
    let a1, ar = dest_disj (concl aOptions) in
    let a2, a3 = dest_disj ar in
    let lt = mk_conj(concl (pt 512 4 (ASSUME `4 IN ooaux c1 c2 a b l 512`)),
                     concl (pt 512 18 (ASSUME `18 IN ooaux c1 c2 a b l 512`))) in
    let rt = mk_conj(concl (pt 512 8 (ASSUME `8 IN ooaux c1 c2 a b l 512`)),
                     concl (pt 512 18 (ASSUME `18 IN ooaux c1 c2 a b l 512`))) in
    let pairA =
      let left = let e = ASSUME a1 in
        DISJ1 (CONJ (pt 512 4 (ccc888_mem_eq e 4)) (pt 512 18 (ccc888_mem_eq e 18))) rt in
      let right a = let e = ASSUME a in
        DISJ2 lt (CONJ (pt 512 8 (ccc888_mem_eq e 8)) (pt 512 18 (ccc888_mem_eq e 18))) in
      DISJ_CASES aOptions left (DISJ_CASES (ASSUME ar) (right a2) (right a3)) in
    let avoid =
      let z = `z:real` in
      let p = MP (SPEC z bottomSegment) (CONJ (ASSUME `&113 / &50 <= z`) (ASSUME `z <= &14 / &5`)) in
      GEN z (DISCH `&113 / &50 <= z` (DISCH `z <= &14 / &5` (foreign 512 8192 p))) in
    ccc888_app CCCPAIR_IMPOSSIBLE (ccc888_pully (ccc888_q 1024) @ ccc888_pully (ccc888_q 512))
      [unit 1024; unit 512; side; markN; inwardN; elbowN; foreign 1024 2304 markNW;
       foreign 1024 16 top12; markA; pairA; foreign 512 rm markR; foreign 512 12 seCorner;
       foreign 512 12 seMarker; avoid; apart 1024 512] in
  let th = DISJ_CASES pattern lower upper in
  if concl th <> `false` then failwith "ccc888_family_impossible" else
  GENL CCC888_VARS (DISCH hyp th);;

(* Lean: family_impossible (b = false: C888) *)
let CCC888_FAMILY_IMPOSSIBLE_F = ccc888_family_impossible false;;
(* Lean: family_impossible (b = true: C889) *)
let CCC888_FAMILY_IMPOSSIBLE_T = ccc888_family_impossible true;;

(* Lean: row888_checked (private) / excludes888 *)
let CCC888_EXCLUDES888 = prove
 (`excl_case 888`,
  REWRITE_TAC[ri_excludes_case_iff 475 `c888d_family_f`; excl_fam] THEN
  MESON_TAC[CCC888_FAMILY_IMPOSSIBLE_F]);;

(* Lean: row889_checked (private) / excludes889 *)
let CCC888_EXCLUDES889 = prove
 (`excl_case 889`,
  REWRITE_TAC[ri_excludes_case_iff 476 `c888d_family_t`; excl_fam] THEN
  MESON_TAC[CCC888_FAMILY_IMPOSSIBLE_T]);;

(* for the assembly: |- EXCLUDED_ROW 475, |- EXCLUDED_ROW 476 *)
let CCC888_EXCLUDED_ROW888 = ri_excluded_row 475 CCC888_EXCLUDES888;;
let CCC888_EXCLUDED_ROW889 = ri_excluded_row 476 CCC888_EXCLUDES889;;

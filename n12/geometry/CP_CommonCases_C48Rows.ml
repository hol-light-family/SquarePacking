(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C48Rows.lean                       *)
(* (N12Compact.CommonCases.C48Rows).  Complete original C48/C573/C574: the   *)
(* NE paired corner supplies a whole vertical segment, and two distinct      *)
(* actual central owners share (1.95, 1.95).  Lean Kind k = c48 | c573 |     *)
(* c574 is the index 0, 1, 2 of the OCaml arrays (C48E_FAM.(k), entrance     *)
(* C48E_ENTRANCE.(k), north_outward C48E_NORTH_OUTWARD.(k)); a theorem       *)
(* stated for all k is the array CCC48R_FAMILY_IMPOSSIBLE of its three       *)
(* instances.  owner p m is (ooc .. m, oos .. m, oou .. m, oov .. m, l);     *)
(* auxiliary_point (with the BasePairs subsets) is oo_aux_point.  Geometry:  *)
(* SouthwestPoint.point = CCSWP_POINT, MergedNearPoint.points_original =     *)
(* CCMNP_POINTS_ORIGINAL, NorthwestSharpPoint.point_original =               *)
(* CCNWS_POINT_ORIGINAL, MergedInwardPoint.point_original =                  *)
(* CCMIP_POINT_ORIGINAL, C981CompletionWallAdvance.point = C981WA_POINT,     *)
(* C981CompletionCornerAdvance.point = C981CA_POINT,                         *)
(* C981CompletionWallOrigin.point = C981WO_POINT; Charts.corner /            *)
(* shiftedTop and their walls are C981CH_INSIDE_CORNER / _SHIFTEDTOP,        *)
(* C981CH_CORNER_WALL / _SHIFTEDTOP_WALL; pullX via LINSIDE_PULLX.           *)
(* ExcludesCase 48 / 573 / 574 at rows 87 / 314 / 315.  Tag CCC48R_.         *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_CommonCases_C48Entrance.ml";;
needs "n12/geometry/CP_CommonCases_SouthwestPoint.ml";;
needs "n12/geometry/CP_CommonCases_MergedNearPoint.ml";;
needs "n12/geometry/CP_CommonCases_NorthwestSharpPoint.ml";;
needs "n12/geometry/CP_CommonCases_MergedInwardPoint.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_C981_WallOrigin.ml";;
needs "n12/geometry/CP_C981_CornerAdvance.ml";;
needs "n12/geometry/CP_C981_Charts.ml";;
needs "n12/geometry/RowIdentity.ml";;

let CCC48R_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let ccc48r_hyp k = mk_conj(`NPACK c1 c2 a b l`, mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, C48E_FAM.(k)));;
let ccc48r_q m = map (fun f -> list_mk_comb(f, CCC48R_VARS @ [mk_small_numeral m]))
                   [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let ccc48r_pull tms q =
  match q with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms
  | _ -> failwith "ccc48r_pull";;
let ccc48r_pullx = ccc48r_pull [`--c:real`; `s:real`; `u - &4 * c`; `--v - a - &4 * s`; `a:real`];;
let ccc48r_corner = ccc48r_pull [`s:real`; `--c:real`; `u - c - &3 * s`; `v + s - &3 * c`; `a:real`];;
let ccc48r_shiftedtop = ccc48r_pull [`c:real`; `s:real`; `u - &2 * c - &3 * s`; `v + &2 * s - &3 * c`; `a:real`];;

let ccc48r_is_rrel t =
  (is_eq t && type_of (lhs t) = `:real`) ||
  (try let op = fst (dest_const (rator (rator t))) in
       (op = "real_lt" || op = "real_le") with Failure _ -> false);;
let CCC48R_DISCH_TAC (asl, w as g) =
  if is_forall w then (REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN ASM_MESON_TAC[]) g else
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         ASM_REWRITE_TAC[] THEN NO_TAC;
         MAP_EVERY (fun (_, th) -> if ccc48r_is_rrel (concl th) then MP_TAC th else ALL_TAC) asl THEN
         REAL_ARITH_TAC] g;;

let CCC48R_CONV = REWRITE_CONV[C981CH_INSIDE_CORNER; C981CH_INSIDE_SHIFTEDTOP; LINSIDE_PULLX; ldisj] THENC
                  ONCE_DEPTH_CONV REAL_RAT_REDUCE_CONV;;

(* apply a geometric lemma to the square tup; facts are normalised like the lemma *)
let ccc48r_app th tup facts =
  let th' = CONV_RULE CCC48R_CONV (SPECL tup th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  let ant = lhand (concl th') in
  let facts = map (CONV_RULE CCC48R_CONV) facts in
  MP th' (TAC_PROOF((map (fun t -> ("", t)) facts, ant), REPEAT CONJ_TAC THEN CCC48R_DISCH_TAC));;

(* |- !z. lo <= z ==> z <= hi ==> P z  (whole horizontal / vertical segment) *)
let ccc48r_seg_all lemma th0 th1 vert =
  let args0 = snd (strip_comb (concl th0)) and args1 = snd (strip_comb (concl th1)) in
  let sq = fst (chop_list 5 args0) in
  let i = if vert then 6 else 5 in
  let fixed = if vert then el 5 args0 else el 6 args0 in
  let th = SPECL (sq @ (if vert then [fixed; el 6 args0; el 6 args1] else [el 5 args0; el 5 args1; fixed]))
             lemma in
  let lt = EQT_ELIM (REAL_RAT_REDUCE_CONV (mk_binop `(<):real->real->bool` (el i args0) (el i args1))) in
  let h0 = mk_binop `(<=):real->real->bool` (el i args0) `z:real`
  and h1 = mk_binop `(<=):real->real->bool` `z:real` (el i args1) in
  GEN `z:real` (DISCH h0 (DISCH h1 (MP (SPEC `z:real` th) (end_itlist CONJ
    [th0; th1; lt; ASSUME h0; ASSUME h1]))));;
let ccc48r_hseg_all = ccc48r_seg_all OO_HORIZONTAL_SEGMENT;;
let ccc48r_at all z =
  let th = SPEC z all in
  let th = MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th)))) in
  MP th (EQT_ELIM (REAL_RAT_REDUCE_CONV (lhand (concl th))));;

(* Lean: family_impossible (for each Kind) *)
let CCC48R_FAMILY_IMPOSSIBLE = Array.init 3 (fun k ->
  let fam = C48E_FAM.(k) in
  let hyp = ccc48r_hyp k in
  let hh = ASSUME hyp in
  let np = CONJUNCT1 hh in
  let mp th = MP (SPECL CCC48R_VARS th) hh in
  let seed m p = mp (oo_inst fam (oo_seed m p)) in
  let apart m n = REWRITE_RULE[ldisj] (mp (oo_apart fam m n)) in
  let foreign m n thn =
    let args = snd (strip_comb (concl thn)) in
    let d = SPECL [el 5 args; el 6 args] (apart m n) in
    let a = lhand (rand (concl d)) in
    NOT_INTRO (DISCH a (MP (NOT_ELIM d) (CONJ (ASSUME a) thn))) in
  let clash m n th1 th2 =
    let args = snd (strip_comb (concl th1)) in
    MP (NOT_ELIM (SPECL [el 5 args; el 6 args] (apart m n))) (CONJ th1 th2) in
  let unit m = MP (SPECL (CCC48R_VARS @ [mk_small_numeral m]) OO_UNIT) np in
  let box m = MP (SPECL (CCC48R_VARS @ [mk_small_numeral m]) OO_BOX) np in
  let side = MP (SPECL CCC48R_VARS OO_SIDE) np in
  let side0 = MP (REAL_ARITH `&1 < l ==> &0 < l`) side in
  let q = ccc48r_q in
  let avoid tm all m n vert =
    let ap = apart m n in
    TAC_PROOF(([], tm), REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun own -> if fst(strip_comb(concl own)) = `linside` then
        let args = snd (strip_comb (concl own)) in
        let x = el 5 args and y = el 6 args in
        MP_TAC(SPEC (if vert then y else x) all) THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
        MP_TAC(SPECL [x; y] ap) THEN ASM_REWRITE_TAC[] else NO_TAC)) in
  let pairs = MP (SPECL CCC48R_VARS C48E_ENTRANCE.(k)) hh in
  let mems = CONJUNCTS (REWRITE_RULE[c48e_basepairs; INSERT_SUBSET; EMPTY_SUBSET] pairs) in
  let pt_from mems m j =
    let mem = find (fun th -> concl th = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j),
                                                list_mk_comb(`ooaux`, CCC48R_VARS @ [mk_small_numeral m]))) mems in
    EQ_MP (SYM (SPECL (CCC48R_VARS @ [mk_small_numeral m]) (oo_aux_point j))) mem in
  let pt = pt_from mems in
  let aP = pt 256 4 and aD = pt 256 13 and iF = pt 8 8 and rF = pt 16384 9 and rG = pt 16384 19 in
  let tF = pt 32768 7 and tG = pt 32768 17 and lF = pt 4096 1 and lG = pt 4096 11 in
  let markA = seed 256 (`&33 / &20`, `&33 / &20`) in
  let markW0 = seed 1536 (`&47 / &20`, `&33 / &20`) and markW1 = seed 1536 (`&47 / &20`, `&47 / &20`) in
  let markN = seed 2048 (`&33 / &20`, `&47 / &20`) and markL = seed 4096 (`&457 / &500`, `&2`) in
  let markR = seed 16384 (`&1543 / &500`, `&2`) and markT = seed 32768 (`&2`, `&1543 / &500`) in
  let cornerK = seed 192 (`&1`, `&3`) and cornerE = seed 48 (`&3`, `&3`) in
  let vDeep = seed 2 (`&19 / &25`, `&187 / &100`) and iDeep = seed 8 (`&81 / &25`, `&187 / &100`) in
  let oLo = seed 1 (`&28 / &25`, `&1`) and oHi = seed 1 (`&87 / &50`, `&1`) in
  let vLo = seed 2 (`&1`, `&28 / &25`) and vHi = seed 2 (`&1`, `&87 / &50`) in
  let oSeg = ccc48r_hseg_all oLo oHi false and vSeg = ccc48r_seg_all OO_VERTICAL_SEGMENT vLo vHi true in
  let aNear = ccc48r_app CCSWP_POINT (q 256)
    [unit 256; side; markA; aP; aD; foreign 256 2 (ccc48r_at vSeg `&33 / &20`); foreign 256 1 oHi;
     foreign 256 1 (ccc48r_at oSeg `&33 / &20`); foreign 256 2 vHi] in
  let wFt = list_mk_comb(`linside`, q 1536 @ [`&2`; `&113 / &50`]) in
  let wF =
    let missing = ASSUME (mk_neg wFt) in
    let wNear = ccc48r_app CCMNP_POINTS_ORIGINAL (q 1536)
      [unit 1536; side; markW0; markW1; foreign 1536 256 aP; missing; foreign 1536 8 iF;
       foreign 1536 16384 rF; foreign 1536 16384 markR] in
    CCONTR wFt (clash 256 1536 aNear (CONJUNCT1 wNear)) in
  let nPair = MP (SPECL CCC48R_VARS C48E_NORTH_OUTWARD.(k)) (CONJ np (CONJ (CONJUNCT2 hh) (CONJ pairs wF))) in
  let nmems = CONJUNCTS (REWRITE_RULE[INSERT_SUBSET; EMPTY_SUBSET] nPair) in
  let nF = pt_from nmems 2048 3 and nG = pt_from nmems 2048 14 in
  let lFar = ccc48r_app C981WA_POINT (q 4096)
    [unit 4096; side; side0; box 4096; markL; lG; foreign 4096 2 vHi; foreign 4096 2 vDeep;
     foreign 4096 2048 markN] in
  let lSeg = ccc48r_seg_all OO_VERTICAL_SEGMENT lF lFar true in
  let rFar = ccc48r_app C981WA_POINT (ccc48r_pullx (q 16384))
    [unit 16384; side; side0; MATCH_MP LCONT_PULLX (box 16384); markR; rG; foreign 16384 8 iF;
     foreign 16384 8 iDeep; foreign 16384 1536 markW1] in
  let e = ccc48r_corner (ccc48r_pullx (q 48)) in
  let eFar = ccc48r_app C981CA_POINT e
    [unit 48; side; side0; MATCH_MP (SPECL (ccc48r_pullx (q 48)) C981CH_CORNER_WALL)
       (MATCH_MP LCONT_PULLX (box 48)); cornerE; foreign 48 16384 rFar; foreign 48 32768 tG] in
  let eSeg = ccc48r_seg_all OO_VERTICAL_SEGMENT cornerE eFar true in
  let t = ccc48r_shiftedtop (q 32768) in
  let avoidE = avoid (list_mk_forall([`z:real`], mk_imp(`&0 <= z /\ z <= &3 / &5`,
                 mk_neg(list_mk_comb(`linside`, q 32768 @ [`&3`; `&3 + z`]))))) eSeg 32768 48 true in
  let tOrigin = ccc48r_app C981WO_POINT t
    [unit 32768; side; side0; MATCH_MP (SPECL (q 32768) C981CH_SHIFTEDTOP_WALL) (box 32768);
     markT; tF; avoidE] in
  let avoidL = avoid (list_mk_forall([`z:real`], mk_imp(`&113 / &50 <= z`, mk_imp(`z <= &14 / &5`,
                 mk_neg(list_mk_comb(`linside`, q 2048 @ [`&1`; `z:real`])))))) lSeg 2048 4096 true in
  let nSharp = ccc48r_app CCNWS_POINT_ORIGINAL (q 2048)
    [unit 2048; side; markN; nF; nG; foreign 2048 1536 wF; foreign 2048 32768 tOrigin;
     foreign 2048 192 cornerK; foreign 2048 32768 markT; avoidL] in
  let wNear = ccc48r_app CCMIP_POINT_ORIGINAL (q 1536)
    [unit 1536; side; markW0; markW1; wF; foreign 1536 256 aP; foreign 1536 8 iF;
     foreign 1536 16384 markR; foreign 1536 2048 nSharp] in
  let th = clash 256 1536 aNear wNear in
  if concl th <> `false` then failwith "CCC48R_FAMILY_IMPOSSIBLE" else
  GENL CCC48R_VARS (DISCH hyp th));;

(* Lean: row48_checked, row573_checked, row574_checked (private) / excludes48, excludes573, excludes574 *)
let CCC48R_ROWS = [| 87; 314; 315 |] and CCC48R_IDS = [| 48; 573; 574 |];;
let CCC48R_EXCLUDES = Array.init 3 (fun k ->
  prove(mk_comb(`excl_case`, mk_small_numeral CCC48R_IDS.(k)),
    REWRITE_TAC[ri_excludes_case_iff CCC48R_ROWS.(k) C48E_FAM.(k); excl_fam] THEN
    MESON_TAC[CCC48R_FAMILY_IMPOSSIBLE.(k)]));;
let CCC48R_EXCLUDES48 = CCC48R_EXCLUDES.(0);;
let CCC48R_EXCLUDES573 = CCC48R_EXCLUDES.(1);;
let CCC48R_EXCLUDES574 = CCC48R_EXCLUDES.(2);;

(* for the assembly: |- EXCLUDED_ROW 87 / 314 / 315 *)
let CCC48R_EXCLUDED_ROW48 = ri_excluded_row 87 CCC48R_EXCLUDES48;;
let CCC48R_EXCLUDED_ROW573 = ri_excluded_row 314 CCC48R_EXCLUDES573;;
let CCC48R_EXCLUDED_ROW574 = ri_excluded_row 315 CCC48R_EXCLUDES574;;

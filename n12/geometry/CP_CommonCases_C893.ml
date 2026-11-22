(* ========================================================================= *)
(* Port of Compact/Completion/CommonCases/C893.lean                          *)
(* (N12Compact.CommonCases.C893).  The complete original C893 contract.     *)
(* Private domains: direct w = restrictByBudget (ofCombined w) is           *)
(* ro_restrict_budget (ro_combined fam n); northGDomain                      *)
(* (HalfDomain.ofTransformedSingletonSpec, swapFG = TOD_SWAPFG, checked by   *)
(* tod_check_points) is tob_transformed_singleton.  The private cuts are     *)
(* stated over the computed allowed lists and decided literally.             *)
(* seed / apart / code / auxiliary_exact / nat_aux_exact: oo_seed, oo_apart, *)
(* HDOM_OWNER, oo_aux_point, oo_auxk_point.  Geometry: InwardPoint.          *)
(* strong_original = CCIP_STRONG_ORIGINAL, C981CompletionWallAdvance.point = *)
(* C981WA_POINT, C981CompletionCrosspoint.point = C981CP_POINT,             *)
(* C893Point.points_original = CCC893_POINTS_ORIGINAL; Transform pulls via   *)
(* LINSIDE_PULLY / LINSIDE_PULLSW.  Row 480.  Tag CCC893C_.                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/CP_CommonCases_C893Point.ml";;
needs "n12/geometry/CP_CommonCases_InwardPoint.ml";;
needs "n12/geometry/CP_C981_WallAdvance.ml";;
needs "n12/geometry/CP_C981_Crosspoint.ml";;
needs "n12/geometry/TransformedOwnerBudget.ml";;
needs "n12/geometry/RowIdentity.ml";;

(* Lean: family *)
let ccc893c_family = new_definition
 `ccc893c_family = {1,2,12,16,192,512,1056,2304,4096,8192,16384,32768}`;;
let CCC893C_F = `ccc893c_family`;;

(* ------------------------------------------------------------------------- *)
(* Literal list cuts (Lean: decide +kernel).                                 *)
(* ------------------------------------------------------------------------- *)

let ccc893c_seteq_conv tm =
  let l, r = dest_eq tm in
  let ls = numset_of l and rs = numset_of r in
  if ls = rs then EQT_INTRO (setlit_eq l r) else
  let e = mk_small_numeral (hd (filter (fun x -> not (mem x rs)) ls @ filter (fun x -> not (mem x ls)) rs)) in
  let th = AP_TERM (mk_comb(`(IN):num->(num->bool)->bool`, e)) (ASSUME tm) in
  let f = CONV_RULE (BINOP_CONV (REWRITE_CONV[IN_INSERT; NOT_IN_EMPTY; ARITH_EQ])) th in
  EQF_INTRO (NOT_INTRO (DISCH tm (EQ_MP (REWRITE_CONV[] (concl f)) f)));;

let CCC893C_DEC_CONV =
  REWRITE_CONV[DISJOINT_INSERT; DISJOINT_EMPTY; INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT;
               NOT_IN_EMPTY; ARITH_EQ; MEM] THENC
  DEPTH_CONV (fun t -> if is_eq t && type_of (lhs t) = `:num->bool` then ccc893c_seteq_conv t
                       else failwith "") THENC
  REWRITE_CONV[];;

let CCC893C_CUT_TAC =
  REWRITE_TAC[MEM] THEN
  TRY(GEN_TAC THEN DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN CONV_TAC CCC893C_DEC_CONV);;

(* !s. MEM s al ==> body s   for the literal allowed list of a domain theorem *)
let ccc893c_cut th body =
  let s = `s:num->bool` in
  prove(mk_forall(s, mk_imp(mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, s), rand (concl th)),
                            body)), CCC893C_CUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Domains.                                                                  *)
(* ------------------------------------------------------------------------- *)

(* Lean: direct (private) *)
let ccc893c_direct n = ro_restrict_budget (ro_combined CCC893C_F n);;

(* Lean: southwestDomain, singletonDomain, bottomDomain, rightDomain, southDomain (private) *)
let CCC893C_SOUTHWEST_DOMAIN = ccc893c_direct 1;;
let CCC893C_SINGLETON_DOMAIN = ccc893c_direct 4;;
let CCC893C_BOTTOM_DOMAIN = ccc893c_direct 19;;
let CCC893C_RIGHT_DOMAIN = ccc893c_direct 21;;
let CCC893C_SOUTH_DOMAIN = ccc893c_direct 8;;

(* Lean: swapFG, swapFG_points, northGDomain (private) *)
let CCC893C_NORTHG_DOMAIN =
  tob_transformed_singleton CCC893C_F 1056 1 0 (true, false, false) 36 TOD_SWAPFG `[{7}; {9}]`;;

(* Lean: singleton_sets (private) *)
let CCC893C_SINGLETON_SETS = CONJ
  (ccc893c_cut CCC893C_SOUTHWEST_DOMAIN `s = {2,12}`)
  (ccc893c_cut CCC893C_SINGLETON_DOMAIN `s = {7,17}`);;
(* Lean: bottom_filtered (private) *)
let CCC893C_BOTTOM_FILTERED = ccc893c_cut CCC893C_BOTTOM_DOMAIN
  `DISJOINT s {2,12} ==> MEM s [{6,15}; {4,6,15}]`;;
(* Lean: right_filtered (private) *)
let CCC893C_RIGHT_FILTERED = ccc893c_cut CCC893C_RIGHT_DOMAIN
  `DISJOINT s {6,15} ==> DISJOINT s {7,17} ==> ~(19 IN s) ==> MEM s [{8,18}; {8,9,18}]`;;
(* Lean: south_filtered (private) *)
let CCC893C_SOUTH_FILTERED = ccc893c_cut CCC893C_SOUTH_DOMAIN
  `DISJOINT s {6,15} ==> DISJOINT s {8,18} ==> {4,16} SUBSET s`;;
(* Lean: checked (local, entrance) *)
let CCC893C_BOTTOM_CHECKED = prove
 (`forall s. MEM s [{6,15}; {4,6,15}] ==> {6,15} SUBSET s`, CCC893C_CUT_TAC);;
let CCC893C_RIGHT_CHECKED = prove
 (`forall s. MEM s [{8,18}; {8,9,18}] ==> {8,18} SUBSET s`, CCC893C_CUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Owner facts under the hypothesis  NPACK .. /\ IMAGE .. = ccc893c_family.  *)
(* ------------------------------------------------------------------------- *)

let CCC893C_VARS = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;
let CCC893C_HYP = `NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc893c_family`;;
let CCC893C_HH = ASSUME CCC893C_HYP;;
let CCC893C_NP = CONJUNCT1 CCC893C_HH;;
let ccc893c_mp th = MP (SPECL CCC893C_VARS th) CCC893C_HH;;
let ccc893c_q m = map (fun f -> list_mk_comb(f, CCC893C_VARS @ [mk_small_numeral m]))
                    [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`];;
let ccc893c_aux m = list_mk_comb(`ooaux`, CCC893C_VARS @ [mk_small_numeral m]);;
let ccc893c_pull tms q =
  match q with
    [c; s; u; v; a] -> map (vsubst [c, `c:real`; s, `s:real`; u, `u:real`; v, `v:real`; a, `a:real`]) tms
  | _ -> failwith "ccc893c_pull";;
let ccc893c_pully = ccc893c_pull [`c:real`; `--s:real`; `u - &4 * s`; `&4 * c - v - a`; `a:real`];;
let ccc893c_pullsw = ccc893c_pull [`s:real`; `c:real`; `u:real`; `--v - a`; `a:real`];;

(* Lean: seed_point (private) *)
let ccc893c_seed m p = ccc893c_mp (oo_inst CCC893C_F (oo_seed m p));;
let ccc893c_apart m n = REWRITE_RULE[ldisj] (ccc893c_mp (oo_apart CCC893C_F m n));;
let ccc893c_foreign m n thn =
  let args = snd (strip_comb (concl thn)) in
  let d = SPECL [el 5 args; el 6 args] (ccc893c_apart m n) in
  let a = lhand (rand (concl d)) in
  NOT_INTRO (DISCH a (MP (NOT_ELIM d) (CONJ (ASSUME a) thn)));;
let ccc893c_unit m = MP (SPECL (CCC893C_VARS @ [mk_small_numeral m]) OO_UNIT) CCC893C_NP;;
let ccc893c_box m = MP (SPECL (CCC893C_VARS @ [mk_small_numeral m]) OO_BOX) CCC893C_NP;;
let CCC893C_SIDE = MP (SPECL CCC893C_VARS OO_SIDE) CCC893C_NP;;
let CCC893C_SIDE0 = MP (REAL_ARITH `&1 < l ==> &0 < l`) CCC893C_SIDE;;
let ccc893c_pt m j memth =
  EQ_MP (SYM (SPECL (CCC893C_VARS @ [mk_small_numeral m]) (oo_aux_point j))) memth;;
let ccc893c_mem_sub sub j =
  find (fun th -> lhand (concl th) = mk_small_numeral j)
    (CONJUNCTS (REWRITE_RULE[INSERT_SUBSET; EMPTY_SUBSET] sub));;
let ccc893c_mem_eq eqth j =
  let t = mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j), lhs (concl eqth)) in
  let r = REWRITE_CONV[eqth; IN_INSERT; NOT_IN_EMPTY; ARITH_EQ] t in
  if rand (concl r) = `true` then EQT_ELIM r else EQF_ELIM r;;
let ccc893c_dom m d =
  MATCH_MP OO_DOMAIN (CONJ d (CONJ CCC893C_NP (CONJ (CONJUNCT2 CCC893C_HH) (in_fam m CCC893C_F))));;
let ccc893c_disj m n =
  MP (SPECL (CCC893C_VARS @ [CCC893C_F; mk_small_numeral m; mk_small_numeral n]) OO_AUX_DISJOINT)
     (end_itlist CONJ [CCC893C_NP; CONJUNCT2 CCC893C_HH; in_fam m CCC893C_F; in_fam n CCC893C_F;
                       EQF_ELIM (NUM_REDUCE_CONV (mk_eq(mk_small_numeral m, mk_small_numeral n)))]);;
let ccc893c_cutth th x ths = List.fold_left MP (SPEC x th) ths;;
let CCC893C_DISJ_MONO = prove
 (`forall s t u:num->bool. DISJOINT s t /\ u SUBSET t ==> DISJOINT s u`, SET_TAC[]);;
let CCC893C_DISJ_MISS = prove
 (`forall s t:num->bool x. DISJOINT s t /\ x IN t ==> ~(x IN s)`, SET_TAC[]);;
let ccc893c_mono d s = MATCH_MP CCC893C_DISJ_MONO (CONJ d s);;
let ccc893c_close hyp_th =
  GENL CCC893C_VARS (DISCH CCC893C_HYP hyp_th);;

let CCC893C_DISCH_TAC =
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         REWRITE_TAC[REAL_MUL_LNEG; REAL_MUL_RNEG; REAL_NEG_NEG] THEN
         (FIRST_ASSUM ACCEPT_TAC ORELSE (ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN FIRST_ASSUM ACCEPT_TAC))];;
let ccc893c_app th tup facts =
  let th' = CONV_RULE (REWRITE_CONV[LINSIDE_PULLY; LINSIDE_PULLSW] THENC REAL_RAT_REDUCE_CONV)
              (SPECL tup th) in
  let th' = if is_neg (concl th') then NOT_ELIM th' else th' in
  let ant = lhand (concl th') in
  MP th' (TAC_PROOF((map (fun t -> ("", t)) facts, ant), REPEAT CONJ_TAC THEN CCC893C_DISCH_TAC));;

let CCC893C_OWN1056 x y = list_mk_comb(`linside`, ccc893c_q 1056 @ [x; y]);;

(* Lean: north_upper (private) *)
let CCC893C_NORTH_UPPER =
  let options = REWRITE_RULE[MEM]
    (MATCH_MP HDOM_OWNER (end_itlist CONJ [CCC893C_NORTHG_DOMAIN; CCC893C_NP; CONJUNCT2 CCC893C_HH;
                                            in_fam 1056 CCC893C_F])) in
  let o1, o2 = dest_disj (concl options) in
  let kpt j e = EQ_MP (SYM (SPECL (CCC893C_VARS @ [`1056`]) (oo_auxk_point 1 j))) (ccc893c_mem_eq e j) in
  let bad = let h = kpt 7 (ASSUME o1) in
    let other = ccc893c_seed 16 (`&113 / &50`, `&3`) in
    CONTR (CCC893C_OWN1056 `&3` `&12 / &5`)
      (MP (NOT_ELIM (SPECL [`&113 / &50`; `&3`] (ccc893c_apart 1056 16))) (CONJ h other)) in
  let good = kpt 9 (ASSUME o2) in
  ccc893c_close (DISJ_CASES options bad good);;

(* Lean: entrance (private) *)
let CCC893C_ENTRANCE =
  let aux = ccc893c_aux and dom = ccc893c_dom and disj = ccc893c_disj and cut = ccc893c_cutth in
  let mono = ccc893c_mono in
  let sw = cut (CONJUNCT1 CCC893C_SINGLETON_SETS) (aux 1) [dom 1 CCC893C_SOUTHWEST_DOMAIN] in
  let tr = cut (CONJUNCT2 CCC893C_SINGLETON_SETS) (aux 16) [dom 16 CCC893C_SINGLETON_DOMAIN] in
  let bottomApart = REWRITE_RULE[sw] (disj 8192 1) in
  let bottomOptions = cut CCC893C_BOTTOM_FILTERED (aux 8192) [dom 8192 CCC893C_BOTTOM_DOMAIN; bottomApart] in
  let bottom = cut CCC893C_BOTTOM_CHECKED (aux 8192) [bottomOptions] in
  let north = MP (SPECL CCC893C_VARS CCC893C_NORTH_UPPER) CCC893C_HH in
  let nineteen = EQ_MP (SPECL (CCC893C_VARS @ [`1056`]) (oo_aux_point 19)) north in
  let missingNineteen = MATCH_MP CCC893C_DISJ_MISS (CONJ (disj 16384 1056) nineteen) in
  let rightBottom = mono (disj 16384 8192) bottom in
  let rightSingleton = REWRITE_RULE[tr] (disj 16384 16) in
  let rightOptions = cut CCC893C_RIGHT_FILTERED (aux 16384)
                       [dom 16384 CCC893C_RIGHT_DOMAIN; rightBottom; rightSingleton; missingNineteen] in
  let right = cut CCC893C_RIGHT_CHECKED (aux 16384) [rightOptions] in
  let south = cut CCC893C_SOUTH_FILTERED (aux 512)
                [dom 512 CCC893C_SOUTH_DOMAIN; mono (disj 512 8192) bottom; mono (disj 512 16384) right] in
  ccc893c_close (end_itlist CONJ [bottom; right; south; north]);;

(* Lean: family_impossible *)
let CCC893C_FAMILY_IMPOSSIBLE =
  let seed = ccc893c_seed and foreign = ccc893c_foreign and pt = ccc893c_pt in
  let sub = ccc893c_mem_sub and unit = ccc893c_unit and side = CCC893C_SIDE in
  let side0 = CCC893C_SIDE0 in
  let ent = MP (SPECL CCC893C_VARS CCC893C_ENTRANCE) CCC893C_HH in
  let bottomAux = CONJUNCT1 ent and southAux = CONJUNCT1 (CONJUNCT2 (CONJUNCT2 ent)) in
  let northUpper = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 ent)) in
  let markerA = seed 512 (`&47 / &20`, `&33 / &20`) in
  let markerN = seed 1056 (`&47 / &20`, `&47 / &20`) in
  let cornerN = seed 1056 (`&1543 / &500`, `&3`) in
  let markerSW = seed 2304 (`&33 / &20`, `&33 / &20`) in
  let markerR = seed 16384 (`&1543 / &500`, `&2`) in
  let tip = seed 16 (`&72 / &25`, `&3`) in
  let inwardA = pt 512 4 (sub southAux 4) in
  let elbowA = pt 512 16 (sub southAux 16) in
  let bottomOuter = pt 8192 6 (sub bottomAux 6) in
  let bottomElbow = pt 8192 15 (sub bottomAux 15) in
  let bottomMarker = seed 8192 (`&2`, `&457 / &500`) in
  let swTip = seed 1 (`&87 / &50`, `&1`) in
  let swSeed = seed 1 (`&187 / &100`, `&19 / &25`) in
  let missingSW = foreign 512 2304 markerSW in
  let missingNE = foreign 512 1056 markerN in
  let missingBottom = foreign 512 8192 bottomOuter in
  let strong = ccc893c_app CCIP_STRONG_ORIGINAL (ccc893c_q 512)
    [unit 512; side; markerA; inwardA; elbowA; missingSW; missingNE; missingBottom] in
  let advance = ccc893c_app C981WA_POINT (ccc893c_pullsw (ccc893c_q 8192))
    [unit 8192; side; side0; MATCH_MP LCONT_PULLSW (ccc893c_box 8192); bottomMarker; bottomOuter;
     foreign 8192 1 swTip; foreign 8192 1 swSeed; foreign 8192 512 markerA] in
  let bottomHalf =
    let args = snd (strip_comb (concl bottomElbow)) in
    MP (SPECL (fst (chop_list 5 args) @ [`&113 / &50`; `&14 / &5`; `&1`; `&5 / &2`]) OO_HORIZONTAL_SEGMENT)
       (end_itlist CONJ [bottomElbow; advance;
          REAL_ARITH `&113 / &50 < &14 / &5`; REAL_ARITH `&113 / &50 <= &5 / &2`;
          REAL_ARITH `&5 / &2 <= &14 / &5`]) in
  let center = ccc893c_app C981CP_POINT (ccc893c_pullsw (ccc893c_pully (ccc893c_q 512)))
    [unit 512; side; side0; elbowA; inwardA; markerA; missingSW; missingNE; missingBottom;
     foreign 512 8192 bottomHalf] in
  let points = ccc893c_app CCC893_POINTS_ORIGINAL (ccc893c_q 1056)
    [unit 1056; side; markerN; northUpper; cornerN; foreign 1056 512 elbowA;
     foreign 1056 16384 markerR; foreign 1056 16 tip] in
  let p1, p2 = dest_disj (concl points) in
  let first = MP (NOT_ELIM (SPECL [`&5 / &2`; `&2`] (ccc893c_apart 512 1056))) (CONJ center (ASSUME p1)) in
  let second = MP (NOT_ELIM (SPECL [`&127 / &50`; `&199 / &100`] (ccc893c_apart 512 1056)))
                  (CONJ strong (ASSUME p2)) in
  let th = DISJ_CASES points first second in
  if concl th <> `false` then failwith "CCC893C_FAMILY_IMPOSSIBLE" else ccc893c_close th;;

(* Lean: row_checked (private) / excludes *)
let CCC893C_EXCLUDES = prove
 (`excl_case 893`,
  REWRITE_TAC[ri_excludes_case_iff 480 `ccc893c_family`; excl_fam] THEN
  MESON_TAC[CCC893C_FAMILY_IMPOSSIBLE]);;

(* for the assembly: |- EXCLUDED_ROW 480 *)
let CCC893C_EXCLUDED_ROW = ri_excluded_row 480 CCC893C_EXCLUDES;;

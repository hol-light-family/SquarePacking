(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/MergedPending/Domains.lean         *)
(* (namespace N12Compact.MergedPending; Lean header: "Source only,           *)
(* uncompiled").  Small ownership deductions for C683 / C700 / C867.        *)
(* Cases are the family constants MPF_FAMILIES (Families.ml); per-case      *)
(* theorems are OCaml lists in the Lean Case order [c683; c700; c867].      *)
(* The private domains xDomain k are mpd_domain fam n = ro_combined fam n    *)
(* (ofCombined combinedSpec n; the budget decides are checked inside);       *)
(* the private cuts are proved over the combinedSpec allowed lists (identical *)
(* for the three families, checked).  CommonLabels p is the predicate        *)
(* mpd_commonLabels c1 c2 a b l.  auxiliaries p m = ooaux c1 c2 a b l m.     *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_MergedPending_Families.ml";;

let MPD_FIVE = [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`];;

(* Lean: southDomain, leftDomain, bottomDomain, topDomain, rightDomain, southeastDomain
   (private), built on demand once per (family, spec) *)
let MPD_DOM_TBL = Hashtbl.create 20;;
let mpd_domain fam n =
  try Hashtbl.find MPD_DOM_TBL (fam, n) with Not_found ->
  let th = ro_combined fam n in Hashtbl.add MPD_DOM_TBL (fam, n) th; th;;

let mpd_allowed n =
  let als = map (fun fam -> rand (concl (mpd_domain fam n))) MPF_FAMILIES in
  if exists (fun al -> al <> hd als) als then failwith "mpd_allowed: lists differ" else hd als;;

let mpd_cut n body =
  let s = `s:num->bool` in
  prove (mk_forall(s, mk_imp(mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, s),
                                     mpd_allowed n), body)),
         OO_LIST_CUT_TAC []);;

(* Lean: south_cut, left_cut, bottom_cut, top_cut, right_cut, southeast_cut, right_upper_cut *)
let MPD_SOUTH_CUT = mpd_cut 6 `~(0 IN s) ==> ~(2 IN s) ==> ~(10 IN s) ==> ~(12 IN s) ==> 4 IN s /\ 13 IN s`;;
let MPD_LEFT_CUT = mpd_cut 17 `~(0 IN s) ==> 1 IN s /\ 11 IN s`;;
let MPD_BOTTOM_CUT = mpd_cut 19 `~(2 IN s) ==> 6 IN s /\ 15 IN s`;;
let MPD_TOP_CUT = mpd_cut 24 `~(7 IN s) ==> 3 IN s /\ 14 IN s`;;
let MPD_RIGHT_CUT = mpd_cut 21 `~(9 IN s) ==> 8 IN s /\ 18 IN s`;;
let MPD_SOUTHEAST_CUT = mpd_cut 8 `~(4 IN s) ==> ~(6 IN s) ==> 8 IN s`;;
let MPD_RIGHT_UPPER_CUT = mpd_cut 21 `~(8 IN s) ==> 9 IN s /\ 19 IN s`;;

(* Lean: foreign_auxiliary (generic in the family; MPD_FOREIGN_AUXILIARY lists the cases) *)
let MPD_FOREIGN_AUXILIARY_GEN = prove
 (`forall c1 c2 a b l fam m n j. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = fam /\
     m IN fam /\ n IN fam /\ ~(m = n) /\ j IN ooaux c1 c2 a b l n
     ==> ~(j IN ooaux c1 c2 a b l m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `fam:num->bool`; `m:num`; `n:num`] OO_AUX_DISJOINT) THEN
  ASM_REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]);;
let MPD_FOREIGN_AUXILIARY =
  map (fun fam -> GENL MPD_FIVE (SPEC fam (SPECL MPD_FIVE MPD_FOREIGN_AUXILIARY_GEN))) MPF_FAMILIES;;

(* Lean: CommonLabels (structure) *)
let mpd_commonLabels = new_definition
 `mpd_commonLabels c1 c2 a b l <=>
    (4 IN ooaux c1 c2 a b l 256 /\ 13 IN ooaux c1 c2 a b l 256) /\
    (1 IN ooaux c1 c2 a b l 4096 /\ 11 IN ooaux c1 c2 a b l 4096) /\
    (6 IN ooaux c1 c2 a b l 8192 /\ 15 IN ooaux c1 c2 a b l 8192) /\
    (3 IN ooaux c1 c2 a b l 32768 /\ 14 IN ooaux c1 c2 a b l 32768)`;;

(* j IN ooaux .. m from a wall / singleton assumption  !x. lo <= x /\ x <= hi ==> linside (owner m) .. *)
let MPD_POINT_MEM_TAC m j =
  SUBGOAL_THEN (mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, mk_small_numeral j), ooaux_tm m))
    ASSUME_TAC THENL
   [REWRITE_TAC[GSYM (oo_aux_point j)] THEN
    FIRST_ASSUM(fun th -> MATCH_MP_TAC th THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC);
    ALL_TAC];;

let mpd_case_tm fam concl =
  list_mk_forall(MPD_FIVE, mk_imp(mk_conj(`NPACK c1 c2 a b l`,
    mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam)), concl));;

(* the singleton memberships F2, G12 of owner 1, F0, G10 of owner 2, F7 of owner 16 *)
let MPD_SINGLETON_TAC fam walls =
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL MPD_FIVE walls) THEN ASM_REWRITE_TAC[mpf_wallData] THEN STRIP_TAC THEN
  MPD_POINT_MEM_TAC 1 2 THEN MPD_POINT_MEM_TAC 1 12 THEN
  MPD_POINT_MEM_TAC 2 0 THEN MPD_POINT_MEM_TAC 2 10 THEN MPD_POINT_MEM_TAC 16 7;;

(* Lean: common_labels (one theorem per case) *)
let MPD_COMMON_LABELS = map2 (fun fam walls ->
  prove (mpd_case_tm fam `mpd_commonLabels c1 c2 a b l`,
    MPD_SINGLETON_TAC fam walls THEN REWRITE_TAC[mpd_commonLabels] THEN
    OO_CHAIN_TAC fam [(256, mpd_domain fam 6); (4096, mpd_domain fam 17);
                      (8192, mpd_domain fam 19); (32768, mpd_domain fam 24)]
      [(256, [4; 13]); (4096, [1; 11]); (8192, [6; 15]); (32768, [3; 14])]))
  MPF_FAMILIES MPF_WALLS;;

(* Lean: c700_right_labels *)
let MPD_C700_RIGHT_LABELS = prove
 (mpd_case_tm `mpf_family_c700` `8 IN ooaux c1 c2 a b l 16384 /\ 18 IN ooaux c1 c2 a b l 16384`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL MPD_FIVE MPF_C700_RIGHT_SINGLETON) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MPD_POINT_MEM_TAC 32 9 THEN
  OO_CHAIN_TAC `mpf_family_c700` [(16384, mpd_domain `mpf_family_c700` 21)] [(16384, [8; 18])]);;

(* Lean: southeast_lower (one theorem per case, each with the hypothesis 512 IN family k) *)
let MPD_SOUTHEAST_LOWER = map2 (fun fam labels ->
  let tm = list_mk_forall(MPD_FIVE, mk_imp(list_mk_conj [`NPACK c1 c2 a b l`;
             mk_eq(`IMAGE binarysum (FFP c1 c2 a b l)`, fam);
             mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, `512`), fam)],
             `8 IN ooaux c1 c2 a b l 512`)) in
  if rhs (concl (in_fam_conv 512 fam)) = `false` then prove (tm, REWRITE_TAC[in_fam_conv 512 fam])
  else
    let dom = mpd_domain fam 8 in
    prove (tm,
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      MP_TAC(SPECL MPD_FIVE labels) THEN ASM_REWRITE_TAC[mpd_commonLabels] THEN STRIP_TAC THEN
      OO_EXCLUDE_ALL_TAC fam 512 THEN OO_DOMAIN_CASES_TAC dom))
  MPF_FAMILIES MPD_COMMON_LABELS;;

(* Lean: c867_right_labels *)
let MPD_C867_RIGHT_LABELS = prove
 (mpd_case_tm `mpf_family_c867` `9 IN ooaux c1 c2 a b l 16384 /\ 19 IN ooaux c1 c2 a b l 16384`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL MPD_FIVE (el 2 MPD_SOUTHEAST_LOWER)) THEN
  ASM_REWRITE_TAC[in_fam 512 `mpf_family_c867`] THEN DISCH_TAC THEN
  OO_CHAIN_TAC `mpf_family_c867` [(16384, mpd_domain `mpf_family_c867` 21)] [(16384, [9; 19])]);;

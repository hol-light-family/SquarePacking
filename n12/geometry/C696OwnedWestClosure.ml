(* ========================================================================= *)
(* Port of Compact/Bridge/C696OwnedWestClosure.lean (namespace N12Compact.   *)
(* C696OwnedWestClosure).  (Lean header: "Source only, uncompiled".)         *)
(* Complete original C696 exclusion.  Conventions of C696CentralNormalForm.ml*)
(* (Data = c696cnf_data, frames A, O with their OpenSquare fields).          *)
(* OwnedWestBottomAngle.small_bottom = OWBA_SMALL_BOTTOM.  Tag C696OWC_.     *)
(* ========================================================================= *)

needs "n12/geometry/C696CentralNormalForm.ml";;
needs "n12/geometry/OwnedWestBottomAngle.ml";;

(* Lean: apart (private) is oo_apart *)

let c696owc_core () =
  let qa = C696CNF_A and qo = C696NBW_O in
  let dt = list_mk_comb(`c696cnf_data`, C696CNF_OLD @ [`l:real`] @ qa @ qo) in
  let [uA; pA; uO; pO; an; aPos; aS; aE; oc; neg; steep; oCan; oS; oE; mcen; westO; _; mc] =
    CONJUNCTS (EQ_MP (SPEC_ALL c696cnf_data) (ASSUME dt)) in
  let on = MP (SPECL [`cO:real`; `sO:real`] C696PBW_NEG_NORMAL)
    (end_itlist CONJ [MP (REAL_ARITH `sO < &0 ==> ~(&0 <= sO)`) neg; oCan; uO]) in
  let os = SYM (SPEC `sO:real` REAL_NEG_NEG) in
  let side = MP (SPECL C696SSP_VARS OO_SIDE) C696SSP_NP in
  let ar = c696ow_arith in
  let same = ar [oS; aS] `aO:real = aA` and sideA = ar [aS; side] `&1 < aA` in
  let box = c696ow_box oE qo 1 in
  let q = c696ck_q in
  let oMarker = c696ow_to oE (q 0 (`&1`, `&457 / &500`) true) in
  let oNear = c696ow_to oE (q 0 (`&28 / &25`, `&1`) true) in
  let oFar = c696ow_to oE (q 0 (`&187 / &100`, `&19 / &25`) true) in
  let oCorner = c696ow_to oE mc in
  let oMissing = c696ow_to oE (q 0 (`&2`, `&457 / &500`) false) in
  let aMarker = c696ow_to aE (q 6 (`&33 / &20`, `&33 / &20`) true) in
  let aD = c696ow_to aE (q 6 (`&2`, `&87 / &50`) true) in
  let aEp = c696ow_to aE (q 6 (`&87 / &50`, `&2`) true) in
  let cross = CONJUNCTS (UNDISCH (SPEC_ALL C696CR_CENTRAL_POINTS)) in
  let aLeft = c696ow_to aE (el 3 cross) and aLow = c696ow_to aE (el 2 cross) in
  let west = c696ow_to aE westO in
  let missingNW = c696ow_to aE (q 6 (`&33 / &20`, `&47 / &20`) false) in
  let foreignLow = c696ow_to aE (q 6 (`&1`, `&8 / &5`) false) in
  let ab = MATCH_MP C977CC_NORMAL_BOUNDS an and an1 = CONJUNCT1 (REWRITE_RULE[c977cc_normal] an) in
  let cap =
    let hi = ASSUME `&2 * (cA + sA) < uA + aA` in
    let lin th = REWRITE_RULE[linside] th in
    let a22 = EQ_MP (SYM (REWRITE_CONV[linside] (c696ow_in qa `&2` `&2`)))
      (c696ow_arith [lin aMarker; lin aD; lin aEp; ab; an1; hi]
         (rhs (concl (REWRITE_CONV[linside] (c696ow_in qa `&2` `&2`))))) in
    let f = MP (NOT_ELIM mcen) (EQ_MP (SPECL [`&2`; `&2`] aE) a22) in
    EQ_MP (REAL_ARITH `~(&2 * (cA + sA) < uA + aA) <=> uA + aA <= &2 * (cA + sA)`)
      (NOT_INTRO (DISCH (concl hi) f)) in
  let oa = c696ow_ldisj oE qo 1 aE qa 256 in
  let small = MP (SPECL (qo @ qa @ [`--sO:real`]) OWBA_SMALL_BOTTOM)
    (end_itlist CONJ [uO; pO; uA; pA; os; on; an; same; sideA; box; oMarker; oNear; oFar; oCorner;
                      oMissing; aMarker; aD; aLeft; aLow; west; cap; missingNW; foreignLow; oa]) in
  let f = MP (REAL_ARITH `--sO < &1 / &5 /\ &1 / &5 < --sO ==> false`) (CONJ small steep) in
  c696wc_fix (GENL (qa @ qo) (DISCH dt f));;

(* Lean: frame_excludes *)
let C696OWC_FRAME_EXCLUDES = GENL C696SSP_VARS (DISCH C696SSP_HYP (c696owc_core ()));;

(* Lean: excludes *)
let C696OWC_EXCLUDES = MP C696CNF_EXCLUDES_OF_NORMAL_FORM C696OWC_FRAME_EXCLUDES;;

(* the assembly form (row 377 of COVER_IDS has id 696) *)
let C696OWC_EXCLUDED_ROW = ri_excluded_row 377 C696OWC_EXCLUDES;;

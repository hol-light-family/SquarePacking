(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1091/EntranceDomains.lean.        *)
(* C1091's actual three-exemption local domains and the covers they force.  *)
(* Owners (Lean owners p i = owner (masks i)) at their literal masks:       *)
(* 0 -> 1, 5 -> 512, 6 -> 1024, 7 -> 2048, 8 -> 4096, 9 -> 8192,           *)
(* 10 -> 16384, 11 -> 32768 (see CP_OtherCases_C1091_OriginalData.ml).      *)
(* The private lemma  bounds  (budget interval of combinedSpec8) is checked *)
(* inside ro_combined; the private  cover  and the decide cuts over the     *)
(* allowed lists are evaluated by OO_DOMAIN_CASES_TAC.                      *)
(* centerX is lcx.  (Lean header: "Source only".)                           *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1091_DirectDomains.ml";;
needs "n12/geometry/CP_OtherCases_C1091_EntranceMergedLow.ml";;
needs "n12/geometry/CP_OtherCases_C1089_ContinuousBottom.ml";;

(* Lean: southeast (ofCombined combinedSpec8; bounds is private) *)
let C1091ED_SOUTHEAST = ro_combined C1091DD_F 8;;

let c1091ed_stmt concl = mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`,
  mk_forall(`b:num->real`, mk_forall(`l:real`,
    mk_imp(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family`, concl))))));;
let c1091ed_stmt_h hyp concl = mk_forall(`c1:num->real`, mk_forall(`c2:num->real`, mk_forall(`a:num->real`,
  mk_forall(`b:num->real`, mk_forall(`l:real`,
    mk_imp(mk_conj(`NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1091od_family`, hyp),
           concl))))));;
let c1091ed_seed m p = oo_inst C1091DD_F (oo_seed m p);;

(* disjunction / conjunction of owner points *)
let C1091ED_COVER_TAC dom js =
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC (map oo_aux_point js) THEN OO_DOMAIN_CASES_TAC dom;;

(* Lean: southeast_f *)
let C1091ED_SOUTHEAST_F = prove
 (c1091ed_stmt (list_mk_disj [own_tm 512 `&2` `&87 / &50`; own_tm 512 `&12 / &5` `&1`;
                              own_tm 512 `&3` `&87 / &50`]),
  C1091ED_COVER_TAC C1091ED_SOUTHEAST [4; 6; 8]);;

(* Lean: southeast_g *)
let C1091ED_SOUTHEAST_G = prove
 (c1091ed_stmt (list_mk_disj [own_tm 512 `&113 / &50` `&1`; own_tm 512 `&113 / &50` `&2`;
                              own_tm 512 `&3` `&8 / &5`]),
  C1091ED_COVER_TAC C1091ED_SOUTHEAST [15; 16; 18]);;

(* Lean: northwest_f *)
let C1091ED_NORTHWEST_F = prove
 (c1091ed_stmt (list_mk_disj [own_tm 2048 `&1` `&113 / &50`; own_tm 2048 `&8 / &5` `&3`;
                              own_tm 2048 `&2` `&113 / &50`]),
  C1091ED_COVER_TAC C1091DD_NORTHWEST [1; 3; 5]);;

(* Lean: northwest_g *)
let C1091ED_NORTHWEST_G = prove
 (c1091ed_stmt (list_mk_disj [own_tm 2048 `&1` `&12 / &5`; own_tm 2048 `&87 / &50` `&2`;
                              own_tm 2048 `&87 / &50` `&3`]),
  C1091ED_COVER_TAC C1091DD_NORTHWEST [11; 13; 14]);;

(* Lean: northeast_f *)
let C1091ED_NORTHEAST_F = prove
 (c1091ed_stmt (list_mk_disj [own_tm 1024 `&2` `&113 / &50`; own_tm 1024 `&12 / &5` `&3`;
                              own_tm 1024 `&3` `&113 / &50`]),
  C1091ED_COVER_TAC C1091DD_NORTHEAST [5; 7; 9]);;

(* Lean: northeast_g *)
let C1091ED_NORTHEAST_G = prove
 (c1091ed_stmt (list_mk_disj [own_tm 1024 `&113 / &50` `&2`; own_tm 1024 `&113 / &50` `&3`;
                              own_tm 1024 `&3` `&12 / &5`]),
  C1091ED_COVER_TAC C1091DD_NORTHEAST [16; 17; 19]);;

(* Lean: bottom_far *)
let C1091ED_BOTTOM_FAR = prove
 (c1091ed_stmt (own_tm 8192 `&12 / &5` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL (c1091ed_seed 1 (`&87 / &50`, `&1`))) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OO_ABSENT_TAC C1091DD_F 8192 12 1 THEN
  REWRITE_TAC[oo_aux_point 6] THEN OO_DOMAIN_CASES_TAC C1091DD_BOTTOM);;

(* Lean: bottom_bar *)
let C1091ED_BOTTOM_BAR = prove
 (c1091ed_stmt (list_mk_conj [mk_binop `(<):real->real->bool` `&51 / &25`
      (list_mk_comb(`lcx`, map (fun f -> list_mk_comb(f, [`c1:num->real`; `c2:num->real`; `a:num->real`;
         `b:num->real`; `l:real`; `8192`])) [`ooc`; `oos`; `oou`; `oov`] @ [`l:real`]));
    own_tm 8192 `&14 / &5` `&1`;
    mk_forall(`x:real`, mk_imp(`&113 / &50 <= x /\ x <= &14 / &5`, own_tm 8192 `x:real` `&1`))]),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1089CB_REACH_OF_FAR THEN
  ASM_SIMP_TAC[OO_UNIT; OO_SIDE; OO_BOX; C1091ED_BOTTOM_FAR; c1091ed_seed 8192 (`&2`, `&457 / &500`);
    oo_excl C1091DD_F 8192 1 (c1091ed_seed 1 (`&87 / &50`, `&1`));
    oo_excl C1091DD_F 8192 1 (c1091ed_seed 1 (`&187 / &100`, `&19 / &25`));
    oo_excl C1091DD_F 8192 512 (c1091ed_seed 512 (`&47 / &20`, `&33 / &20`))]);;

(* Lean: left_pair *)
let C1091ED_LEFT_PAIR = prove
 (c1091ed_stmt (mk_conj(own_tm 4096 `&1` `&113 / &50`, own_tm 4096 `&1` `&12 / &5`)),
  MESON_TAC[C1091DD_LEFT_PAIR; OC1091EML_ORIGINAL]);;

(* Lean: right_high_pair *)
let C1091ED_RIGHT_HIGH_PAIR = prove
 (c1091ed_stmt_h (mk_neg (own_tm 16384 `&3` `&87 / &50`))
    (mk_conj(own_tm 16384 `&3` `&113 / &50`, own_tm 16384 `&3` `&12 / &5`)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(8 IN ooaux c1 c2 a b l 16384)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM (oo_aux_point 8)]; ALL_TAC] THEN
  REWRITE_TAC[oo_aux_point 9; oo_aux_point 19] THEN OO_DOMAIN_CASES_TAC C1091DD_RIGHT);;

(* Lean: top_f7 *)
let C1091ED_TOP_F7 = prove
 (c1091ed_stmt_h (mk_neg (own_tm 32768 `&8 / &5` `&3`)) (own_tm 32768 `&12 / &5` `&3`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(3 IN ooaux c1 c2 a b l 32768)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM (oo_aux_point 3)]; ALL_TAC] THEN
  REWRITE_TAC[oo_aux_point 7] THEN OO_DOMAIN_CASES_TAC C1091DD_TOP);;

(* Lean: top_component *)
let C1091ED_TOP_COMPONENT = prove
 (c1091ed_stmt (mk_disj(own_tm 32768 `&113 / &50` `&3`,
                        mk_conj(own_tm 32768 `&8 / &5` `&3`, own_tm 32768 `&87 / &50` `&3`))),
  C1091ED_COVER_TAC C1091DD_TOP [17; 3; 14]);;

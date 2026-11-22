(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/C1089/DirectDomains.lean            *)
(* (namespace N12Compact.Completion.OtherCases.C1089.DirectDomains).         *)
(* Four small combined local certificates on the actual C1089 family         *)
(* (family = c1089sc_family, true three-exemption budgets).  Owners: Lean    *)
(* owners p i = owner (EL i c1089sc_masks): 0 -> 1, 8 -> 4096, 9 -> 8192,    *)
(* 10 -> 16384, 11 -> 32768.  ofCombined = ro_combined (its private bounds   *)
(* lower = 1, upper = 2 are computed and checked by the producer; Lean       *)
(* AuxiliaryCover.exemption_count = C1089DD_EXEMPTION_COUNT), cached_domain =*)
(* cdom_cache / cdom_named.  The C997Domains lists bottomAllowed /          *)
(* rightAllowed / topAllowed are the literal lists of C997D_BOTTOM / RIGHT / *)
(* TOP (copied; C997Domains itself is not loaded).  The private cut lemmas   *)
(* are evaluated inside OO_DOMAIN_CASES_TAC; auxiliary_exact = oo_aux_point. *)
(* (Lean header: "Source only, uncompiled".)  Tag C1089DD_.                  *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1089_OriginalData.ml";;
needs "n12/geometry/CP_CommonCases_OriginalOwners.ml";;
needs "n12/geometry/RelaxedOwnerDomain.ml";;

let C1089DD_F = `c1089sc_family`;;

(* Lean: AuxiliaryCover.exemption_count *)
let C1089DD_EXEMPTION_COUNT = prove
 (`forall k. k < 2 ==> CARD (c1089sc_family INTER auxex k) = 3`,
  REWRITE_TAC[ARITH_RULE `k < 2 <=> k = 0 \/ k = 1`] THEN GEN_TAC THEN
  DISCH_THEN (DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[card_exempt C1089DD_F 0; card_exempt C1089DD_F 1]);;

(* Lean: leftAllowed *)
let c1089dd_left_allowed = new_definition
 `c1089dd_left_allowed : (num->bool)list =
    [{0,10}; {0,10,13}; {1,11}; {1,11,13}; {0,1,10}; {0,1,11};
     {0,1,10,11}; {0,1,10,13}; {0,1,11,13}; {0,2,10}; {1,3,11}]`;;

(* Lean: left, bottom, right, top *)
let C1089DD_LEFT = cdom_named (ro_combined C1089DD_F 17) c1089dd_left_allowed;;
let C1089DD_BOTTOM = cdom_cache (ro_combined C1089DD_F 19) `[{2,12}; {2,10,12}; {2,12,15}; {6,15}; {6,12,15}; {6,15,18}; {2,4,12}; {2,4,12,15}; {2,6,12,15}; {4,6,15}; {4,6,12,15}]`;;
let C1089DD_RIGHT = cdom_cache (ro_combined C1089DD_F 21) `[{8,18}; {8,16,18}; {9,19}; {9,16,19}; {6,8,18}; {7,9,19}; {8,9,18}; {8,9,19}; {8,9,16,18}; {8,9,16,19}; {8,9,18,19}]`;;
let C1089DD_TOP = cdom_cache (ro_combined C1089DD_F 24) `[{3,14}; {3,11,14}; {3,14,17}; {7,17}; {7,14,17}; {7,17,19}; {3,5,14}; {3,5,14,17}; {3,7,14,17}; {5,7,17}; {5,7,14,17}]`;;

let c1089dd_own m x y = list_mk_comb(`linside`,
  map (fun f -> list_mk_comb(f, C1089SC_VARS @ [mk_small_numeral m])) [`ooc`; `oos`; `oou`; `oov`] @
  [`l:real`; x; y]);;
let c1089dd_stmt hyps body =
  list_mk_forall(C1089SC_VARS,
    mk_imp(list_mk_conj ([`NPACK c1 c2 a b l`; `IMAGE binarysum (FFP c1 c2 a b l) = c1089sc_family`] @ hyps),
           body));;
let C1089DD_TAC pts dth =
  REPEAT GEN_TAC THEN REWRITE_TAC (map oo_aux_point pts) THEN STRIP_TAC THEN OO_DOMAIN_CASES_TAC dth;;

(* Lean: right_points *)
let C1089DD_RIGHT_POINTS = prove
 (c1089dd_stmt [`~(8 IN ooaux c1 c2 a b l 16384)`]
    (mk_conj(c1089dd_own 16384 `&3` `&113 / &50`, c1089dd_own 16384 `&3` `&12 / &5`)),
  C1089DD_TAC [9; 19] C1089DD_RIGHT);;

(* Lean: top_component *)
let C1089DD_TOP_COMPONENT = prove
 (c1089dd_stmt []
    (mk_disj(c1089dd_own 32768 `&113 / &50` `&3`,
             mk_conj(c1089dd_own 32768 `&8 / &5` `&3`, c1089dd_own 32768 `&87 / &50` `&3`))),
  C1089DD_TAC [17; 3; 14] C1089DD_TOP);;

(* Lean: bottom_far *)
let C1089DD_BOTTOM_FAR = prove
 (c1089dd_stmt [] (c1089dd_own 8192 `&12 / &5` `&1`),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (SPEC_ALL (c1089od_seed 0 (`&87 / &50`, `&1`))) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  OO_ABSENT_TAC C1089DD_F 8192 12 1 THEN
  REWRITE_TAC[oo_aux_point 6] THEN OO_DOMAIN_CASES_TAC C1089DD_BOTTOM);;

(* Lean: left_pair *)
let C1089DD_LEFT_PAIR = prove
 (c1089dd_stmt [mk_neg (c1089dd_own 4096 `&1` `&87 / &50`)]
    (mk_conj(c1089dd_own 4096 `&1` `&113 / &50`, c1089dd_own 4096 `&1` `&12 / &5`)),
  C1089DD_TAC [0; 1; 11] C1089DD_LEFT);;

(* Lean: right_low_pair *)
let C1089DD_RIGHT_LOW_PAIR = prove
 (c1089dd_stmt [mk_neg (c1089dd_own 16384 `&3` `&113 / &50`)]
    (mk_conj(c1089dd_own 16384 `&3` `&87 / &50`, c1089dd_own 16384 `&3` `&8 / &5`)),
  C1089DD_TAC [9; 8; 18] C1089DD_RIGHT);;

(* Lean: right_high_pair *)
let C1089DD_RIGHT_HIGH_PAIR = prove
 (c1089dd_stmt [mk_neg (c1089dd_own 16384 `&3` `&87 / &50`)]
    (mk_conj(c1089dd_own 16384 `&3` `&113 / &50`, c1089dd_own 16384 `&3` `&12 / &5`)),
  REWRITE_TAC[oo_aux_point 8] THEN MESON_TAC[C1089DD_RIGHT_POINTS]);;

(* Lean: top_g_cover *)
let C1089DD_TOP_G_COVER = prove
 (c1089dd_stmt []
    (mk_disj(c1089dd_own 32768 `&87 / &50` `&3`, c1089dd_own 32768 `&113 / &50` `&3`)),
  C1089DD_TAC [14; 17] C1089DD_TOP);;

(* Lean: top_f7 *)
let C1089DD_TOP_F7 = prove
 (c1089dd_stmt [mk_neg (c1089dd_own 32768 `&8 / &5` `&3`)] (c1089dd_own 32768 `&12 / &5` `&3`),
  C1089DD_TAC [3; 7] C1089DD_TOP);;

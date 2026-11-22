(* ========================================================================= *)
(* Phase 2: Compact/Completion/OtherCases/C1090/DirectDomains.lean           *)
(* (namespace N12Compact.Completion.OtherCases.C1090.DirectDomains; Lean     *)
(* header: "Source only, uncompiled").  The two combined local certificates  *)
(* right (spec 21, mask 16384 = owners p 10) and top (spec 24, mask 32768 =  *)
(* owners p 11) at the actual C1090 family, as theorems                      *)
(*   |- cdom c1090od_family mask [allowed]                                   *)
(* with the C997Domains rightAllowed / topAllowed lists.  The private bounds *)
(* lemma (budget 1..2 from exemption_count = C1090AC_EXEMPTION_COUNT) is      *)
(* checked inside ro_combined; cached_domain = cdom_cache.  The cut lemmas   *)
(* quantify over the literal allowed lists (decide +kernel = OO_LIST_CUT_TAC).*)
(* Tag C1090DD_.                                                             *)
(* ========================================================================= *)

needs "n12/geometry/CP_OtherCases_C1090_AuxiliaryCover.ml";;
needs "n12/geometry/CP_FiniteCases_C997Domains.ml";;

let c1090dd_al th = rand (concl th);;

(* Lean: bounds (private) — checked inside ro_combined *)

(* Lean: right *)
let C1090DD_RIGHT = cdom_cache (ro_combined C1090OD_F 21) (c1090dd_al C997D_RIGHT);;

(* Lean: top *)
let C1090DD_TOP = cdom_cache (ro_combined C1090OD_F 24) (c1090dd_al C997D_TOP);;

let c1090dd_cut al body =
  let s = `s:num->bool` in
  prove (mk_forall(s, mk_imp(mk_comb(mk_comb(`MEM:(num->bool)->(num->bool)list->bool`, s), al), body)),
         OO_LIST_CUT_TAC []);;

(* Lean: right_cut (private) *)
let C1090DD_RIGHT_CUT = c1090dd_cut (c1090dd_al C997D_RIGHT) `~(8 IN s) ==> 9 IN s /\ 19 IN s`;;

(* Lean: top_cut (private) *)
let C1090DD_TOP_CUT = c1090dd_cut (c1090dd_al C997D_TOP) `17 IN s \/ (3 IN s /\ 14 IN s)`;;

(* Lean: right_points *)
let C1090DD_RIGHT_POINTS = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1090od_family /\
     ~(8 IN ooaux c1 c2 a b l 16384)
     ==> linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384)
                 (oov c1 c2 a b l 16384) l (&3) (&113 / &50) /\
         linside (ooc c1 c2 a b l 16384) (oos c1 c2 a b l 16384) (oou c1 c2 a b l 16384)
                 (oov c1 c2 a b l 16384) l (&3) (&12 / &5)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[oo_aux_point 9; oo_aux_point 19] THEN OO_DOMAIN_CASES_TAC C1090DD_RIGHT);;

(* Lean: top_component *)
let C1090DD_TOP_COMPONENT = prove
 (`forall c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c1090od_family
     ==> linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
                 (oov c1 c2 a b l 32768) l (&113 / &50) (&3) \/
         (linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
                  (oov c1 c2 a b l 32768) l (&8 / &5) (&3) /\
          linside (ooc c1 c2 a b l 32768) (oos c1 c2 a b l 32768) (oou c1 c2 a b l 32768)
                  (oov c1 c2 a b l 32768) l (&87 / &50) (&3))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[oo_aux_point 17; oo_aux_point 3; oo_aux_point 14] THEN OO_DOMAIN_CASES_TAC C1090DD_TOP);;

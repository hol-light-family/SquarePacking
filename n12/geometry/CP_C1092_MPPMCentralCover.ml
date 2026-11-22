(* ========================================================================= *)
(* Port of Compact/Completion/C1092/MPPMCentralCover.lean                    *)
(* (N12Compact.C1092MPPMCentralCover).  The exhaustive actual southwest      *)
(* central cover in the zero-omission MPPM entrance.  Conventions of         *)
(* CP_C1092_MPPMEntrance.ml / CP_C1092_MPPMOmissions.ml: owners p i is the   *)
(* OriginalOwners 5-tuple at mask EL i c1092wc_code (side l); WallContext p  *)
(* mppm is c1092wc_ctx c1 c2 a b l c1092mppe_mppm; Missing is                *)
(* c1092mom_missing.  central_cover_transported at (T,F,F) / southwest_g_   *)
(* cover: C1092AuxiliaryCover.ml; C1092MixedSpan.impossible C1092MS_IMPOSSIBLE*)
(* (applied to pullX (owners p 4) via the c1092mo_ layer toolkit of          *)
(* CP_C1092_MMMP_Origins.ml, which only uses NPACK / IMAGE here).            *)
(* Tag C1092MCC_.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/CP_C1092_MPPMOmissions.ml";;
needs "n12/geometry/C1092AuxiliaryCover.ml";;
needs "n12/geometry/CP_C1092_MixedSpan.ml";;
needs "n12/geometry/CP_C1092_MMMP_Origins.ml";;

(* Lean: Ordinary *)
let c1092mcc_ordinary = new_definition
 `c1092mcc_ordinary (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    linside c s u v a (&1) (&87 / &50) /\ linside c s u v a (&1) (&8 / &5)`;;

(* Lean: Inward *)
let c1092mcc_inward = new_definition
 `c1092mcc_inward (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    linside c s u v a (&2) (&87 / &50) /\ linside c s u v a (&87 / &50) (&2)`;;

(* Lean: Elbow *)
let c1092mcc_elbow = new_definition
 `c1092mcc_elbow (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    linside c s u v a (&1) (&87 / &50) /\ linside c s u v a (&87 / &50) (&2) /\
    ~linside c s u v a (&1) (&8 / &5) /\ ~linside c s u v a (&2) (&87 / &50)`;;

let C1092MCC_OWN4 = c1092ae_own C1092AE_P 4;;
let C1092MCC_CONCL = Printf.sprintf "c1092mcc_ordinary %s \\/ c1092mcc_inward %s \\/ c1092mcc_elbow %s"
  C1092MCC_OWN4 C1092MCC_OWN4 C1092MCC_OWN4;;

(* central_cover_transported at (T,F,F), owner 4 *)
let C1092MCC_SW_COVER = c1092ac_concrete C1092AC_CENTRAL_COVER_TRANSPORTED `(true,false,false)` 4
  [`&1`, `&87 / &50`; `&8 / &5`, `&1`; `&2`, `&87 / &50`];;

(* Lean: cover *)
let C1092MCC_COVER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ %s ==> %s" C1092AE_P C1092AE_HYP
    (c1092mppe_in 9 "&8 / &5" "&1") (c1092mppe_in 9 "&87 / &50" "&1") C1092MCC_CONCL),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[c1092mcc_ordinary; c1092mcc_inward; c1092mcc_elbow] THEN
  CONV_TAC C1092MO_CODE_CONV THEN RULE_ASSUM_TAC(CONV_RULE C1092MO_CODE_CONV) THEN
  let useh th = CONV_RULE C1092MO_CODE_CONV (MP (SPECL C1092MMPE_V th) (c1092mo_hh ())) in
  let bF = ASSUME (c1092mo_in 9 `&8 / &5` `&1`) and bG = ASSUME (c1092mo_in 9 `&87 / &50` `&1`) in
  let ccov = useh C1092MCC_SW_COVER and gcov = useh C1092AC_SOUTHWEST_G_COVER in
  let eF = c1092mo_excl 4 9 bF and eG = c1092mo_excl 4 9 bG in
  let t, eqs = c1092mo_layers 4 [C1092MO_X] in
  let hF2 = c1092mo_in 4 `&2` `&87 / &50` and hF1 = mk_neg (c1092mo_in 4 `&1` `&87 / &50`)
  and hG1 = c1092mo_in 4 `&1` `&8 / &5` and hG2 = mk_neg (c1092mo_in 4 `&87 / &50` `&2`) in
  let ms = itlist DISCH [hF2; hF1; hG1; hG2]
    (c1092mo_apply (c1092mo_conv eqs) (SPECL t C1092MS_IMPOSSIBLE)
      [c1092mo_punit 4 t; c1092mo_pos (); c1092mo_side ();
       ASSUME hF2; ASSUME hF1; ASSUME hG1; ASSUME hG2; eF; eG]) in
  MP_TAC (end_itlist CONJ [ccov; gcov; eF; eG; ms]) THEN CONV_TAC TAUT);;

(* Lean: no_omission_cover *)
let C1092MCC_NO_OMISSION_COVER = prove
 (parse_term (Printf.sprintf "!%s. %s /\\ %s /\\ (!k. k < 4 ==> ~c1092mom_missing c1 c2 a b l k) ==> %s"
    C1092AE_P C1092AE_HYP C1092MPPE_CTX C1092MCC_CONCL),
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC C1092MCC_COVER THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC_ALL C1092MOM_ORDINARY_WALLS) THEN ASM_SIMP_TAC[]);;

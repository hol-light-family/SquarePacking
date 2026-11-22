(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeInward.lean (N12Compact.C868 and  *)
(* N12Compact.C868.UpperNegativeInward, Jatloe).                             *)
(* MergedPending.NegativeUpperFaces Input / lower_v / top_marker_faces /     *)
(* top_lower_tilt = ocmpnuf_input / OCMPNUF_*; Normal = c977cc_normal;       *)
(* CanonicalProjection.before = CCCP_BEFORE.                                 *)
(* A square H is cH sH uH vH aH (unit normal, positive side); Lean           *)
(* H.translated 2 2 is (cH, sH, uH - (cH * &2 + sH * &2),                    *)
(*   vH - (--sH * &2 + cH * &2), aH).  Lean owner p m = OriginalOwners tuple. *)
(* Also: the small packing toolkit (C868UI_INTRO_TAC, C868UI_IFF_TAC, ...)    *)
(* used by the other C868 UpperNegative* files.  Tag C868UI_.                *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_MergedPending_NegativeUpperFaces.ml";;
needs "n12/geometry/CP_CommonCases_CanonicalProjection.ml";;
needs "n12/geometry/Cases_C868_Ownership.ml";;
needs "n12/geometry/SoutheastGeometry.ml";;

(* Lean: S12.inside_translated_iff *)
let C868UI_INSIDE_TRANSLATED = prove
 (`forall c s u v a x y p q.
      linside c s (u - (c * x + s * y)) (v - (--s * x + c * y)) a p q <=>
      linside c s u v a (x + p) (y + q)`,
  REWRITE_TAC[linside] THEN REAL_ARITH_TAC);;

(* unpack an assumption  ocmpnuf_input c s u v a  (kept) into linear facts *)
let C868UI_INPUT_TAC =
  FIRST_ASSUM(fun th ->
    if fst(strip_comb(concl th)) = `ocmpnuf_input` then
      let th1 = REWRITE_RULE[ocmpnuf_input] th in
      let nb = MATCH_MP C977CC_NORMAL_BOUNDS (CONJUNCT1 th1) in
      ASSUME_TAC (CONJUNCT1 th1) THEN
      STRIP_ASSUME_TAC (REWRITE_RULE[c977cc_normal; linside] th1) THEN
      STRIP_ASSUME_TAC nb
    else NO_TAC);;

(* specialise a lemma, discharge its antecedent from the assumptions or by
   (linear) arithmetic, and add the conjuncts of its conclusion *)
let C868UI_DISCH_TAC =
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE (CONV_TAC REAL_RAT_REDUCE_CONV THEN NO_TAC) ORELSE
   NLIN_TAC ~deg2:false []);;
let C868UI_USE tms th =
  MP_TAC (SPECL tms th) THEN ANTS_TAC THENL
   [C868UI_DISCH_TAC; DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))];;

(* goal  linside ...  closed against the assumption  ~linside ... *)
let C868UI_POINT_TAC t =
  UNDISCH_TAC t THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];;

(* unfold the positive linside assumptions (negations are kept) *)
let C868UI_UNFOLD_TAC =
  RULE_ASSUM_TAC(fun th -> if is_neg(concl th) then th else REWRITE_RULE[linside] th);;

let C868UI_SQ = [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`];;

(* Lean: UpperNegativeInward.top_upper_v *)
let C868UI_TOP_UPPER_V = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\ ocmpnuf_input c s u v a /\
     ~linside c s u v a (&13 / &50) (&0) /\
     ~linside c s u v a (&1 / &2) (&0)
     ==> v + a <= &543 / &500 * c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  C868UI_USE C868UI_SQ OCMPNUF_TOP_MARKER_FACES THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
  [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  C868UI_USE C868UI_SQ OCMPNUF_LOWER_V THEN
  C868UI_USE C868UI_SQ OCMPNUF_TOP_LOWER_TILT THEN
  C868UI_INPUT_TAC THEN
  ASM_CASES_TAC `&35 * c <= --(&61) * s` THENL
  [C868UI_POINT_TAC `~linside c s u v a (&13 / &50) (&0)`;
   C868UI_USE [`c:real`; `--s`; `&56 / &65`; `&33 / &65`; `&1 / &2`; `&543 / &500`]
     CCCP_BEFORE THEN
   C868UI_POINT_TAC `~linside c s u v a (&1 / &2) (&0)`]);;

(* ------------------------------------------------------------------------- *)
(* Packing toolkit.  Statements:  !c1 c2 a b l [vars]. NPACK c1 c2 a b l /\   *)
(* IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\ hyps ==> P.            *)
(* C868UI_INTRO_TAC assumes C868_H (so the Ownership facts, whose hypothesis *)
(* is C868_H, can be used directly) and every further hypothesis.            *)
(* ------------------------------------------------------------------------- *)

let C868UI_INTRO_TAC =
  REPEAT GEN_TAC THEN DISCH_THEN(fun th ->
    let cs = CONJUNCTS th in
    ASSUME_TAC (CONJ (el 0 cs) (el 1 cs)) THEN MAP_EVERY ASSUME_TAC (tl (tl cs)));;

(* rewrite with the assumptions  !x y. linside H x y <=> linside (owner) x y *)
let C868UI_IFF_TAC =
  ASSUM_LIST(fun ths -> REWRITE_TAC(filter (fun th ->
    let t = snd(strip_forall(concl th)) in is_forall(concl th) && is_iff t &&
      fst(strip_comb(lhand t)) = `linside`) ths));;

(* translated square goals: unfold the translation and normalise the points *)
let C868UI_TRANSLATE_TAC =
  REWRITE_TAC[C868UI_INSIDE_TRANSLATED] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  C868UI_IFF_TAC;;

(* close a goal from facts (theorems with hypothesis C868_H) *)
let C868UI_FACTS_TAC facts =
  MAP_EVERY ASSUME_TAC facts THEN REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_REWRITE_TAC[C868_SIDE]);;

(* apply a packing theorem  !c1 c2 a b l [vs]. NPACK .. /\ IMAGE .. /\ hs ==> P
   (vs instantiated by name) to C868_H and the given hypothesis theorems *)
let c868ui_app th hyps =
  let th1 = SPEC_ALL (SPECL C868OW_VARS th) in
  let avail = CONJUNCTS (ASSUME C868_H) @ hyps in
  let rec build t =
    try find (fun f -> aconv (concl f) t) avail with Failure _ ->
    if is_conj t then CONJ (build (lhand t)) (build (rand t))
    else failwith ("c868ui_app: " ^ string_of_term t) in
  MP th1 (build (lhand (concl th1)));;

(* ~linside (owner m) x y  from  linside (owner n) x y  (any hypotheses) *)
let c868ui_excl m n thn =
  let d = REWRITE_RULE[ldisj] (c868_apart_f m n) in
  let args = snd(strip_comb(concl thn)) in
  let d1 = SPECL [el 5 args; el 6 args] d in
  MP (MP (TAUT (mk_imp(concl d1, mk_imp(concl thn, mk_neg(lhand(rand(concl d1))))))) d1) thn;;

(* add the conclusion of a packing theorem, hypotheses from the assumptions *)
let C868UI_APP_TAC th =
  ASSUM_LIST(fun ths -> MAP_EVERY ASSUME_TAC (CONJUNCTS (c868ui_app th ths)));;

(* owner tuple terms *)
let c868ui_owner m = c868_own m;;
let c868ui_lin m x y = list_mk_comb(`linside`, c868_own m @ [x; y]);;

(* Lean: negative_upper_input *)
let C868UI_NEGATIVE_UPPER_INPUT = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cH (--sH) /\ aH = l /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y)
     ==> ocmpnuf_input cH sH (uH - (cH * &2 + sH * &2)) (vH - (--sH * &2 + cH * &2)) aH`,
  C868UI_INTRO_TAC THEN REWRITE_TAC[ocmpnuf_input] THEN C868UI_TRANSLATE_TAC THEN
  C868UI_FACTS_TAC
   [c868_seed_f 3072 (`&33 / &20`, `&47 / &20`);
    c868_seed_f 3072 (`&47 / &20`, `&47 / &20`);
    c868_excl_f 3072 256 (c868_forced_f 1);
    c868_excl_f 3072 32768 (c868_forced_f 2);
    c868_excl_f 3072 32768 (c868_seed_f 32768 (`&2`, `&1543 / &500`))]);;

(* Lean: negative_upper_inward_top_cap *)
let C868UI_NEGATIVE_UPPER_INWARD_TOP_CAP = prove
 (`forall c1 c2 a b l cH sH uH vH aH.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     cH * cH + sH * sH = &1 /\ &0 < aH /\
     c977cc_normal cH (--sH) /\ aH = l /\
     (forall x y. linside cH sH uH vH aH x y <=>
            linside (ooc c1 c2 a b l 3072) (oos c1 c2 a b l 3072) (oou c1 c2 a b l 3072)
                    (oov c1 c2 a b l 3072) l x y) /\
     linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
             (oov c1 c2 a b l 512) l (&113 / &50) (&2)
     ==> (vH - (--sH * &2 + cH * &2)) + aH <= &543 / &500 * cH`,
  C868UI_INTRO_TAC THEN C868UI_APP_TAC C868UI_NEGATIVE_UPPER_INPUT THEN
  MP_TAC(SPECL [`cH:real`; `sH:real`; `uH - (cH * &2 + sH * &2)`;
                `vH - (--sH * &2 + cH * &2)`; `aH:real`] C868UI_TOP_UPPER_V) THEN
  DISCH_THEN MATCH_MP_TAC THEN C868UI_TRANSLATE_TAC THEN
  let inward = ASSUME (c868ui_lin 512 `&113 / &50` `&2`) in
  C868UI_FACTS_TAC
   [c868ui_excl 3072 512 inward;
    c868ui_excl 3072 512 (c868ui_app C868SE_SOUTHEAST_RIGHT_CROSSPOINT [inward])]);;

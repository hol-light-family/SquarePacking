(* ========================================================================= *)
(* Port of Compact/Bridge/C977Residual.lean (N12Compact.C977Residual).       *)
(* The exact remaining original C977 cover (no whole-case exclusion).        *)
(* Conventions of C977PositiveBottomWest.ml / C977OuterWings.ml:             *)
(* p.square (orderedOwner p i) is the 5-tuple c977cre_sq i, natCombined-     *)
(* Owners p (orderedOwner p 5) is ooaux c1 c2 a b l (EL 5 c977av_code); the  *)
(* family q : Fin 12 -> OpenSquare is five functions qc qs qu qv qa with     *)
(* the OpenSquare invariants (unit normal, positive side) for i < 12.        *)
(* SignedEscape p is c977res_signed c1 c2 a b l, Alternatives p is           *)
(* c977res_alt c1 c2 a b l.  ExcludesCase 977 is excl_case 977               *)
(* (CCC977RI_EXCLUDES_CASE_IFF).  WallOwners / WallHalfSpaces /              *)
(* StrengthenedMissingCorner / CanonicalCornerBounds / actualAuxiliaryVector *)
(* / remainingVectors as in C977OW_CANONICAL_REMAINING_COVER.  Tag C977RES_.  *)
(* ========================================================================= *)

needs "n12/geometry/C977OuterWings.ml";;
needs "n12/geometry/C977PositiveBottomWest.ml";;
needs "n12/geometry/CC_C977_RowIdentity.ml";;

(* Lean: SignedEscape *)
let c977res_signed = new_definition (parse_term (Printf.sprintf
  "c977res_signed c1 c2 a b l <=>
     ~linside %s (&2) (&2) /\\
     ?qc qs qu qv qa.
       (!i. i < 12 ==> qc i * qc i + qs i * qs i = &1 /\\ &0 < qa i) /\\
       (!i. i < 12 ==> &0 < qc i /\\ abs (qs i) <= qc i) /\\
       (!i. i < 12 ==> qa i = l) /\\
       (!i x y. i < 12 ==> (linside (qc i) (qs i) (qu i) (qv i) (qa i) x y <=> linside %s x y)) /\\
       qs 0 < &0 /\\ &0 < qs 5 /\\ linside %s (&1) (&1) /\\
       ooaux c1 c2 a b l (EL 5 c977av_code) = {4, 13}"
  (c977cre_sq 5) (c977pco_sqv "i") (c977cre_sq 1)));;

(* Lean: Alternatives *)
let c977res_alt = new_definition (parse_term (Printf.sprintf
  "c977res_alt c1 c2 a b l <=> linside %s (&2) (&2) \\/ c977res_signed c1 c2 a b l"
  (c977cre_sq 5)));;

(* Lean: escape_signature (private) *)
let C977RES_ESCAPE_SIGNATURE = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l cA sA uA vA aA. %s /\\ cA * cA + sA * sA = &1 /\\ &0 < aA /\\
      c977cc_normal cA sA /\\ &0 < sA /\\
      (!x y. linside cA sA uA vA aA x y <=> linside %s x y) /\\
      ~linside %s (&2) (&2)
      ==> ooaux c1 c2 a b l (EL 5 c977av_code) = {4, 13}"
   C977CRE_HYP (c977cre_sq 5) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  let eqA = ASSUME (parse_term (Printf.sprintf
    "!x y. linside cA sA uA vA aA x y <=> linside %s x y" (c977cre_sq 5))) in
  MP_TAC(ASSUME `c977cc_normal cA sA`) THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(MATCH_MP C977CC_NORMAL_BOUNDS th) THEN
                       STRIP_ASSUME_TAC(REWRITE_RULE[c977cc_normal] th)) THEN
  MAP_EVERY (fun (x, y) ->
    let e = SPECL [x; y] eqA in
    STRIP_ASSUME_TAC(REWRITE_RULE[linside] (EQ_MP (SYM e) (ASSUME (rand(concl e))))))
   [(`&33 / &20`, `&33 / &20`); (`&2`, `&87 / &50`); (`&87 / &50`, `&2`)] THEN
  (* cap *)
  SUBGOAL_THEN `uA + aA <= &2 * (cA + sA)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC (parse_term (Printf.sprintf "~linside %s (&2) (&2)" (c977cre_sq 5))) THEN
    REWRITE_TAC[GSYM eqA] THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  (* noTop, noRight *)
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "~linside %s (&2) (&113 / &50) /\\ ~linside %s (&113 / &50) (&2)"
    (c977cre_sq 5) (c977cre_sq 5))) MP_TAC THENL
   [REWRITE_TAC[GSYM eqA; linside] THEN CONJ_TAC THEN STRIP_TAC THEN NLIN_TAC ~deg2:false [];
    ALL_TAC] THEN
  C977WC_TO_OO_TAC 5 THEN REWRITE_TAC[oo_aux_point 5; oo_aux_point 16] THEN
  REWRITE_TAC[IMP_CONJ] THEN C977WC_DOMAIN_CASES_TAC 5);;

let C977RES_COMPS_I =
  let w = "(c977av_ordered_owner c1 c2 a b l i)" in
  map parse_term
   [Printf.sprintf "(a:num->real) %s" w; Printf.sprintf "(b:num->real) %s" w;
    Printf.sprintf "a %s * c1 %s + b %s * (c2:num->real) %s - l / &2" w w w w;
    Printf.sprintf "--b %s * c1 %s + a %s * (c2:num->real) %s - l / &2" w w w w; "l:real"];;

(* Lean: alternatives *)
let C977RES_ALTERNATIVES = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s /\\ ~linside %s (&1) (&1) ==> c977res_alt c1 c2 a b l"
   C977CRE_HYP (c977cre_sq 0)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[c977res_alt] THEN
  ASM_CASES_TAC (parse_term (Printf.sprintf "linside %s (&2) (&2)" (c977cre_sq 5))) THEN
  ASM_REWRITE_TAC[c977res_signed] THEN
  (* the canonical frames of all twelve squares *)
  SUBGOAL_THEN (parse_term (Printf.sprintf
    "!i. ?c' s' u' v' a'. i < 12 ==>
       c' * c' + s' * s' = &1 /\\ &0 < a' /\\ &0 < c' /\\ abs s' <= c' /\\ a' = l /\\
       (!x y. linside c' s' u' v' a' x y <=> linside %s x y)" (c977pco_sqv "i")))
    MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i < 12` THEN ASM_REWRITE_TAC[EXISTS_SIMP] THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  `c977av_ordered_owner c1 c2 a b l i`] NPACK_SQ) THEN
    REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
    MP_TAC(SPECL C977RES_COMPS_I CLF_CANONICAL_FRAME) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `qc:num->real` (X_CHOOSE_THEN `qs:num->real` (X_CHOOSE_THEN `qu:num->real`
    (X_CHOOSE_THEN `qv:num->real` (X_CHOOSE_THEN `qa:num->real` ASSUME_TAC))))) THEN
  SUBGOAL_THEN (parse_term (Printf.sprintf "%s /\\ (!i. i < 12 ==> &0 < qc i /\\ abs (qs i) <= qc i)"
    C977PBW_QHYP)) STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                `qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`]
    C977PBW_FRAME_RESIDUAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> &0 < qc i /\ abs (qs i) <= qc i`) (concl th)
      then MP_TAC(CONJ (SPEC `0` th) (SPEC `5` th)) else NO_TAC) THEN
    REWRITE_TAC[ARITH] THEN SIMP_TAC[];
    STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC [`qc:num->real`; `qs:num->real`; `qu:num->real`; `qv:num->real`; `qa:num->real`] THEN
  ASM_REWRITE_TAC[] THEN
  C977PBW_Q_TAC 5 THEN
  FIRST_ASSUM(fun th -> if can (term_match [] `forall i. i < 12 ==> &0 < qc i /\ abs (qs i) <= qc i`) (concl th)
    then STRIP_ASSUME_TAC(REWRITE_RULE[ARITH] (SPEC `5` th)) else NO_TAC) THEN
  MATCH_MP_TAC C977RES_ESCAPE_SIGNATURE THEN
  MAP_EVERY EXISTS_TAC [`(qc:num->real) 5`; `(qs:num->real) 5`; `(qu:num->real) 5`; `(qv:num->real) 5`; `(qa:num->real) 5`] THEN
  ASM_REWRITE_TAC[c977cc_normal; REAL_POW_2] THEN RASM_ARITH_TAC);;

let C977RES_SQD0 =
  let w = "(c977av_ordered_owner d1 d2 e1 e2 l 0)" in
  Printf.sprintf "(e1 %s) (e2 %s) (e1 %s * d1 %s + e2 %s * d2 %s - l / &2) (--e2 %s * d1 %s + e1 %s * d2 %s - l / &2) l"
    w w w w w w w w w w;;

(* Lean: canonical_remaining_cover *)
let C977RES_CANONICAL_REMAINING_COVER = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. NPACK c1 c2 a b l /\\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family
   ==> ?d1 d2 e1 e2.
  ((d1,d2,e1,e2) = (c1,c2,a,b) \\/ (d1,d2,e1,e2) = (c2,c1,b,a)) /\\
  NPACK d1 d2 e1 e2 l /\\ IMAGE binarysum (FFP d1 d2 e1 e2 l) = ccc977ri_family /\\
  c977mcp_strengthened %s /\\ c977mcb_ccb %s /\\
  ?w. c977wb_owners d1 d2 e1 e2 l w /\\
      c977wb_half d1 d2 e1 e2 l w (c977wc_expand (F,F)) /\\
      MEM (c977av_actual d1 d2 e1 e2 l) c977ow_remaining /\\
      c977res_alt d1 d2 e1 e2 l" C977RES_SQD0 C977RES_SQD0),
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP C977OW_CANONICAL_REMAINING_COVER) THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `w:num->num` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C977RES_ALTERNATIVES THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> fst (strip_comb (concl th)) = `c977mcp_strengthened`)) THEN
  SIMP_TAC[c977mcp_strengthened; c977cr_mce]);;


(* Lean: excludes_case_of_two_endings *)
let C977RES_EXCLUDES_CASE_OF_TWO_ENDINGS = prove
 (parse_term (Printf.sprintf
   "(!c1 c2 a b l. NPACK c1 c2 a b l /\\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\\
       c977mcp_strengthened %s /\\ c977mcb_ccb %s
       ==> !w. c977wb_owners c1 c2 a b l w /\\
               c977wb_half c1 c2 a b l w (c977wc_expand (F,F)) /\\
               MEM (c977av_actual c1 c2 a b l) c977ow_remaining
               ==> (linside %s (&2) (&2) ==> F) /\\ (c977res_signed c1 c2 a b l ==> F))
    ==> excl_case 977"
   (c977cre_sq 0) (c977cre_sq 0) (c977cre_sq 5)),
  DISCH_TAC THEN REWRITE_TAC[CCC977RI_EXCLUDES_CASE_IFF; excl_fam] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP C977RES_CANONICAL_REMAINING_COVER) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`d1:num->real`; `d2:num->real`; `e1:num->real`; `e2:num->real`; `l:real`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:num->num`) THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> fst (strip_comb (concl th)) = `c977res_alt`)) THEN
  REWRITE_TAC[c977res_alt] THEN CONV_TAC TAUT);;

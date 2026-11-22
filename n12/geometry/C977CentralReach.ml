(* ========================================================================= *)
(* Port of Compact/Bridge/C977CentralReach.lean (N12Compact.C977CentralReach).*)
(* Two simultaneous strict points of the original C977 southwest central    *)
(* owner.  Conventions of AuxiliaryVectors.ml: orderedOwner p i is           *)
(* c977av_ordered_owner c1 c2 a b l i, p.square j is the 5-tuple            *)
(* (a j) (b j) (a j * c1 j + b j * c2 j - l / &2)                            *)
(* (--b j * c1 j + a j * c2 j - l / &2) l, natCombinedOwners p              *)
(* (orderedOwner p i) is ooaux c1 c2 a b l (EL i c977av_code); the owner of  *)
(* mask 256 = EL 5 c977av_code is the OriginalOwners tuple (ooc .. 256).     *)
(* SouthwestCentralReach.below / left: SWCR_BELOW / SWCR_LEFT;               *)
(* code_one_anchors / code_two_original_anchors: C977AN_ lemmas.  Tag C977CRE_.*)
(* ========================================================================= *)

needs "n12/geometry/SouthwestCentralReach.ml";;
needs "n12/geometry/AuxiliaryContext.ml";;
needs "n12/geometry/Anchors.ml";;

let c977cre_sq i =
  let w = Printf.sprintf "(c977av_ordered_owner c1 c2 a b l %d)" i in
  Printf.sprintf "(a %s) (b %s) (a %s * c1 %s + b %s * c2 %s - l / &2) (--b %s * c1 %s + a %s * c2 %s - l / &2) l"
    w w w w w w w w w w;;

let C977CRE_HYP = "NPACK c1 c2 a b l /\\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family";;

(* the ordered owner i is the original owner of its code *)
let C977CRE_ORDERED_OOIDX = prove
 (`forall c1 c2 a b l i. c977av_ordered_owner c1 c2 a b l i = oidx c1 c2 a b l (EL i c977av_code)`,
  REWRITE_TAC[c977av_ordered_owner]);;

let C977CRE_TO_OO_TAC i =
  REWRITE_TAC[C977CRE_ORDERED_OOIDX; C977AV_CODE_EL.(i)] THEN
  REWRITE_TAC[GSYM oou; GSYM oov] THEN REWRITE_TAC[GSYM ooc; GSYM oos];;

(* Lean: forced_auxiliary (private) *)
let C977CRE_FORCED_AUXILIARY = prove
 (`forall c1 c2 a b l n. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     (forall os. MEM os (EL 5 c977av_prune4) ==> n IN os)
     ==> n IN ooaux c1 c2 a b l (EL 5 c977av_code)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977AV_PRUNED_AUXILIARY_DOMAIN_ACTUAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `5`) THEN REWRITE_TAC[ARITH]);;

let C977CRE_P5 = (REWRITE_CONV[c977av_prune4] THENC ONCE_DEPTH_CONV EL_CONV) `EL 5 c977av_prune4`;;

let C977CRE_FORCED_IN n =
  let th = SPEC n (SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
                    C977CRE_FORCED_AUXILIARY) in
  let side = prove(lhand(rand(lhand(concl th))) |> (fun _ ->
      mk_forall(`os:num->bool`, mk_imp(`MEM (os:num->bool) (EL 5 c977av_prune4)`,
        mk_comb(mk_comb(`(IN):num->(num->bool)->bool`, n), `os:num->bool`)))),
    REWRITE_TAC[C977CRE_P5; MEM] THEN GEN_TAC THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV) in
  REWRITE_RULE[side; C977AV_CODE_EL.(5)] th;;

(* Lean: central_data *)
let C977CRE_CENTRAL_DATA = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s ==> linside %s (&33 / &20) (&33 / &20) /\\ linside %s (&2) (&87 / &50) /\\
      linside %s (&87 / &50) (&2) /\\ ~linside %s (&47 / &20) (&47 / &20) /\\
      ~linside %s (&33 / &20) (&47 / &20) /\\ ~linside %s (&47 / &20) (&33 / &20)"
   C977CRE_HYP (c977cre_sq 5) (c977cre_sq 5) (c977cre_sq 5) (c977cre_sq 5) (c977cre_sq 5) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN C977CRE_TO_OO_TAC 5 THEN
  let inst th = MP (SPEC_ALL (oo_inst `ccc977ri_family` th))
                   (CONJ (ASSUME `NPACK c1 c2 a b l`)
                         (ASSUME `IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family`)) in
  REWRITE_TAC[oo_aux_point 4; oo_aux_point 13] THEN
  REPEAT CONJ_TAC THENL
   [ACCEPT_TAC(inst (oo_seed 256 (`&33 / &20`, `&33 / &20`)));
    MATCH_MP_TAC (C977CRE_FORCED_IN `4`) THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC (C977CRE_FORCED_IN `13`) THEN ASM_REWRITE_TAC[];
    MP_TAC(inst (oo_missing 256 10)) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    MP_TAC(inst (oo_missing 256 11)) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[];
    MP_TAC(inst (oo_missing 256 9)) THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]]);;

(* Lean: apart (private) *)
let C977CRE_APART = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l j. %s /\\ j < 12 /\\ ~(5 = j) ==>
      ldisj %s (a (c977av_ordered_owner c1 c2 a b l j)) (b (c977av_ordered_owner c1 c2 a b l j))
        (a (c977av_ordered_owner c1 c2 a b l j) * c1 (c977av_ordered_owner c1 c2 a b l j) +
         b (c977av_ordered_owner c1 c2 a b l j) * c2 (c977av_ordered_owner c1 c2 a b l j) - l / &2)
        (--b (c977av_ordered_owner c1 c2 a b l j) * c1 (c977av_ordered_owner c1 c2 a b l j) +
         a (c977av_ordered_owner c1 c2 a b l j) * c2 (c977av_ordered_owner c1 c2 a b l j) - l / &2) l"
   C977CRE_HYP (c977cre_sq 5)),
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NPACK_LDISJ THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977AV_ORDERED_OWNER_INJECTIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPECL [`5`; `j:num`]) THEN
  ASM_REWRITE_TAC[ARITH]);;

(* Lean: central_points *)
let C977CRE_CENTRAL_POINTS = prove
 (parse_term (Printf.sprintf
   "!c1 c2 a b l. %s ==> linside %s (&2) (&3 / &2) /\\ linside %s (&3 / &2) (&2)"
   C977CRE_HYP (c977cre_sq 5) (c977cre_sq 5)),
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`]
    C977CRE_CENTRAL_DATA) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  let own i = mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(mk_comb(`c977av_ordered_owner`,
                `c1:num->real`), `c2:num->real`), `a:num->real`), `b:num->real`), `l:real`),
                mk_small_numeral i) in
  let facts i =
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; own i]
      NPACK_SQ) THEN
    ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN
    REWRITE_TAC[GSYM c977av_ordered_owner] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  mk_small_numeral i] C977AV_ORDERED_OWNER_CODE) THEN
    ASM_REWRITE_TAC[C977AV_CODE_EL.(i); ARITH] THEN DISCH_TAC THEN
    (if i = 5 then ALL_TAC else
    MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`;
                  mk_small_numeral i] C977CRE_APART) THEN
    ASM_REWRITE_TAC[ARITH] THEN DISCH_TAC) in
  facts 5 THEN facts 1 THEN facts 0 THEN
  SUBGOAL_THEN `&0 < l` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; own 1]
    C977AN_CODE_TWO_ORIGINAL_ANCHORS) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; own 0]
    C977AN_CODE_ONE_ANCHORS) THEN
  ASM_REWRITE_TAC[c977av_ordered_owner; OIDX_LT] THEN
  REWRITE_TAC[GSYM c977av_ordered_owner; c977mcg_anchors] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC SWCR_BELOW; MATCH_MP_TAC SWCR_LEFT] THEN
  FIRST_ASSUM(fun th ->
    if can (term_match [] `ldisj c s u v a c' s' u' v' a'`) (concl th) then
      let args = snd(strip_comb(concl th)) in
      MAP_EVERY EXISTS_TAC (map (fun i -> el i args) [5; 6; 7; 8; 9]) THEN
      ASM_REWRITE_TAC[] THEN NO_TAC
    else failwith ""));;

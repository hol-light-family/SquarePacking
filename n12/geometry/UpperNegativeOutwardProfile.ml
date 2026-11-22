(* ========================================================================= *)
(* Port of Compact/Cases/C868/UpperNegativeOutwardProfile.lean               *)
(* (N12Compact.C868 and N12Compact.C868.UpperNegativeOutward, Jatloe).       *)
(* Faces = c868op_faces; OutwardBarFrame.faces_original =                     *)
(* OCOBF_FACES_ORIGINAL (on pullY B: LINSIDE_PULLY); B.translated 2 2 is     *)
(* (cB, sB, uB - (cB * &2 + sB * &2), vB - (--sB * &2 + cB * &2), aB).        *)
(* Lean  ∃ B : OpenSquare, ...  is  ?cB sB uB vB aB. cB * cB + sB * sB = &1  *)
(* /\ &0 < aB /\ ...                                                          *)
(* Tag C868OP_.                                                              *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/SoutheastGeometry.ml";;
needs "n12/geometry/CP_OtherCases_OutwardBarFrame.ml";;
needs "n12/geometry/C977CornerCubic.ml";;

(* Lean: UpperNegativeOutward.Faces (structure) *)
let c868op_faces = new_definition
 `c868op_faces (c:real) s u v a <=>
    c977cc_normal c (--s) /\ &1 < a /\
    &13 / &50 * c <= u /\
    --(&4 / &5) * s - c <= v /\
    u + a <= c - s /\
    v + a <= --(&543 / &500) * s /\
    &1 < c - &143 / &500 * s /\
    &1 < &37 / &50 * c - s`;;

(* Lean: UpperNegativeOutward.faces_original *)
let C868OP_FACES_ORIGINAL = prove
 (`forall c s u v a.
     c * c + s * s = &1 /\ &0 < a /\
     c977cc_normal c (--s) /\ &1 < a /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     linside c s u v a (&3) (&87 / &50) /\
     ~linside c s u v a (&113 / &50) (&2) /\
     ~linside c s u v a (&1543 / &500) (&2) /\
     ~linside c s u v a (&3) (&1) /\
     ~linside c s u v a (&1543 / &500) (&1) /\
     (forall x. &113 / &50 <= x ==> x <= &14 / &5 ==> ~linside c s u v a x (&1))
     ==> c868op_faces c s (u - (c * &2 + s * &2)) (v - (--s * &2 + c * &2)) a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP C977CC_NORMAL_BOUNDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977cc_normal] o
    check (fun th -> fst(strip_comb(concl th)) = `c977cc_normal`)) THEN
  MP_TAC(SPECL [`c:real`; `--s`; `u - &4 * s`; `&4 * c - v - a`; `a:real`]
    OCOBF_FACES_ORIGINAL) THEN
  REWRITE_TAC[LINSIDE_PULLY; REAL_NEG_NEG] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[REAL_NEG_MUL2] THEN RASM_ARITH_TAC;
   REWRITE_TAC[ocobp_faces; c868op_faces] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN RASM_ARITH_TAC]);;

(* Lean: southeast_outward_profile *)
let C868OP_SOUTHEAST_OUTWARD_PROFILE = prove
 (`forall c1 c2 a b l.
     NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = c868_family /\
     ~linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
              (oov c1 c2 a b l 512) l (&113 / &50) (&2)
     ==> exists cB sB uB vB aB.
           cB * cB + sB * sB = &1 /\ &0 < aB /\ aB = l /\
           (forall x y. linside cB sB uB vB aB x y <=>
                  linside (ooc c1 c2 a b l 512) (oos c1 c2 a b l 512) (oou c1 c2 a b l 512)
                          (oov c1 c2 a b l 512) l x y) /\
           c868op_faces cB sB (uB - (cB * &2 + sB * &2)) (vB - (--sB * &2 + cB * &2)) aB`,
  C868SE_INTRO_TAC THEN C868SE_APP_TAC C868SE_SOUTHEAST_OUTWARD_FRAME THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `cB:real` (X_CHOOSE_THEN `sB:real` (X_CHOOSE_THEN `uB:real`
    (X_CHOOSE_THEN `vB:real` (X_CHOOSE_THEN `aB:real` STRIP_ASSUME_TAC)))) o
    check (is_exists o concl)) THEN
  MAP_EVERY EXISTS_TAC [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`] THEN
  REPEAT(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
  MATCH_MP_TAC (SPECL [`cB:real`; `sB:real`; `uB:real`; `vB:real`; `aB:real`]
    C868OP_FACES_ORIGINAL) THEN
  C868SE_IFF_TAC THEN
  SUBGOAL_THEN `c977cc_normal cB (--sB)` ASSUME_TAC THENL
  [REWRITE_TAC[c977cc_normal; REAL_POW_2; REAL_NEG_MUL2] THEN
   REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE RASM_ARITH_TAC);
   ALL_TAC] THEN
  let bar =
    let x = `x:real` in
    let lo = ASSUME `&113 / &50 <= x` and hi = ASSUME `x <= &14 / &5` in
    GEN x (DISCH (concl lo) (DISCH (concl hi)
      (c868se_excl 512 8192 (c868se_app C868AB_BOTTOM_BAR [lo; hi])))) in
  C868SE_FACTS_TAC
   [c868_seed_f 512 (`&47 / &20`, `&33 / &20`);
    c868_mp C868AO_ADDITIONAL_INSIDE.(7);
    c868_excl_f 512 16416 (c868_seed_f 16416 (`&1543 / &500`, `&2`));
    c868_excl_f 512 12 (c868_seed_f 12 (`&3`, `&1`));
    c868_excl_f 512 12 (c868_seed_f 12 (`&1543 / &500`, `&1`));
    bar]);;

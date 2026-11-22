(* ========================================================================= *)
(* Phase 2: Completion/Cases/C977/InteriorFaces.lean.                        *)
(* Conventions of WallBranches.ml / MissingCornerPoints.ml: p.square i is    *)
(* the 5-tuple (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)                *)
(* (--b i * c1 i + a i * c2 i - l / &2) l; family is ccc977ri_family.        *)
(* PositiveFrameOf q r is c977if_pframe q r (q, r as 5-tuples; the          *)
(* OpenSquare fields of r, unit normal and positive side, are stated         *)
(* separately in the existentials).  TenUpperU / TenUpperV / TenLowerV are   *)
(* c977if_tenuu / c977if_tenuv / c977if_tenlv.  S12.exists_positive_frame is *)
(* WCB_EXISTS_POSITIVE_FRAME (WallCenterBarrier.ml).  Tag C977IF_.           *)
(* ========================================================================= *)

needs "n12/geometry/WallBranches.ml";;
needs "n12/geometry/WallCenterBarrier.ml";;

(* Lean: PositiveFrameOf (structure) *)
let c977if_pframe = new_definition
 `c977if_pframe (c:real) (s:real) (u:real) (v:real) (a:real)
                (c':real) (s':real) (u':real) (v':real) (a':real) <=>
    &0 <= c' /\ &0 <= s' /\ a' = a /\
    lcx c' s' u' v' a' = lcx c s u v a /\ lcy c' s' u' v' a' = lcy c s u v a /\
    (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)`;;

(* Lean: positive_frame_of *)
let C977IF_POSITIVE_FRAME_OF = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
                          c977if_pframe c s u v a c' s' u' v' a'`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP WCB_EXISTS_POSITIVE_FRAME) THEN
  REWRITE_TAC[c977if_pframe] THEN MESON_TAC[]);;

(* Lean: TenUpperU *)
let c977if_tenuu = new_definition
 `c977if_tenuu (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    u + a <= c * (&47 / &20) + s * (&47 / &20)`;;

(* Lean: TenUpperV *)
let c977if_tenuv = new_definition
 `c977if_tenuv (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    v + a <= --s * (&47 / &20) + c * (&47 / &20)`;;

(* Lean: TenLowerV *)
let c977if_tenlv = new_definition
 `c977if_tenlv (c:real) (s:real) (u:real) (v:real) (a:real) <=>
    --s * (&47 / &20) + c * (&47 / &20) <= v`;;

let C977IF_FACE_TAC =
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c977if_tenuu; c977if_tenuv; c977if_tenlv; linside] THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;;

(* Lean: marker_nine_ten_faces *)
let C977IF_MARKER_NINE_TEN_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\
     linside c s u v a (&47 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&47 / &20)
     ==> c977if_tenuu c s u v a \/ c977if_tenuv c s u v a`,
  C977IF_FACE_TAC);;

(* Lean: marker_eleven_ten_faces *)
let C977IF_MARKER_ELEVEN_TEN_FACES = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\
     linside c s u v a (&33 / &20) (&47 / &20) /\
     ~linside c s u v a (&47 / &20) (&47 / &20)
     ==> c977if_tenuu c s u v a \/ c977if_tenlv c s u v a`,
  C977IF_FACE_TAC);;

(* Lean: marker_eight_ten_faces_ge *)
let C977IF_MARKER_EIGHT_TEN_FACES_GE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\ s <= c /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&47 / &20)
     ==> c977if_tenuu c s u v a \/ c977if_tenuv c s u v a`,
  C977IF_FACE_TAC);;

(* Lean: marker_eight_ten_faces_le *)
let C977IF_MARKER_EIGHT_TEN_FACES_LE = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\ c <= s /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&47 / &20)
     ==> c977if_tenuu c s u v a \/ c977if_tenlv c s u v a`,
  C977IF_FACE_TAC);;

(* Lean: marker_eight_ten_faces_eq *)
let C977IF_MARKER_EIGHT_TEN_FACES_EQ = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\ c = s /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&47 / &20)
     ==> c977if_tenuu c s u v a`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c977if_tenuu; linside] THEN
  REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `c:real = s`)) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM; REAL_NOT_LE] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* Lean: marker_eight_ten_face_cover *)
let C977IF_MARKER_EIGHT_TEN_FACE_COVER = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a /\ &0 <= c /\ &0 <= s /\
     linside c s u v a (&33 / &20) (&33 / &20) /\
     ~linside c s u v a (&47 / &20) (&47 / &20)
     ==> (s <= c /\ (c977if_tenuu c s u v a \/ c977if_tenuv c s u v a)) \/
         (c <= s /\ (c977if_tenuu c s u v a \/ c977if_tenlv c s u v a))`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(REAL_ARITH `s <= c \/ c <= s:real`) THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C977IF_MARKER_EIGHT_TEN_FACES_GE THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C977IF_MARKER_EIGHT_TEN_FACES_LE THEN ASM_REWRITE_TAC[]]);;

(* the owned marker k and the missing marker 10 of the singleton square i of code m *)
let C977IF_CODE_FACTS = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12
     ==> a i * a i + b i * b i = &1 /\ &0 < l /\
         (ownmask (c1 i) (c2 i) (a i) (b i) l = 512
          ==> linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                      (--b i * c1 i + a i * c2 i - l / &2) l (&47 / &20) (&33 / &20)) /\
         (ownmask (c1 i) (c2 i) (a i) (b i) l = 2048
          ==> linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                      (--b i * c1 i + a i * c2 i - l / &2) l (&33 / &20) (&47 / &20)) /\
         (ownmask (c1 i) (c2 i) (a i) (b i) l = 256
          ==> linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                      (--b i * c1 i + a i * c2 i - l / &2) l (&33 / &20) (&33 / &20)) /\
         ~linside (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                  (--b i * c1 i + a i * c2 i - l / &2) l (&47 / &20) (&47 / &20)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    NPACK_SQ) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977WB_UNUSED_MARKER_TEN) THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977CR_CODED_EXACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `9`); FIRST_X_ASSUM(MP_TAC o SPEC `11`);
    FIRST_X_ASSUM(MP_TAC o SPEC `8`)] THEN
  ASM_REWRITE_TAC[MARKER_EXPLICIT; VECTOR_2; bitset_bits 512; bitset_bits 2048; bitset_bits 256;
                  IN_SET_OF_LIST; MEM] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

let C977IF_CODE_TAC face_th =
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c1:num->real`; `c2:num->real`; `a:num->real`; `b:num->real`; `l:real`; `i:num`]
    C977IF_CODE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`(a:num->real) i`; `(b:num->real) i`;
                `(a:num->real) i * (c1:num->real) i + (b:num->real) i * (c2:num->real) i - l / &2`;
                `--(b:num->real) i * (c1:num->real) i + (a:num->real) i * (c2:num->real) i - l / &2`;
                `l:real`] C977IF_POSITIVE_FRAME_OF) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[c977if_pframe] o
              check (fun th -> try fst (strip_comb (concl th)) = `c977if_pframe` with _ -> false)) THEN
  face_th;;

(* Lean: code_512_ten_faces *)
let C977IF_CODE_512_TEN_FACES = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 512
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           c977if_pframe (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                         (--b i * c1 i + a i * c2 i - l / &2) l c' s' u' v' a' /\
           (c977if_tenuu c' s' u' v' a' \/ c977if_tenuv c' s' u' v' a')`,
  C977IF_CODE_TAC
   (MATCH_MP_TAC C977IF_MARKER_NINE_TEN_FACES THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]));;

(* Lean: code_2048_ten_faces *)
let C977IF_CODE_2048_TEN_FACES = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 2048
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           c977if_pframe (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                         (--b i * c1 i + a i * c2 i - l / &2) l c' s' u' v' a' /\
           (c977if_tenuu c' s' u' v' a' \/ c977if_tenlv c' s' u' v' a')`,
  C977IF_CODE_TAC
   (MATCH_MP_TAC C977IF_MARKER_ELEVEN_TEN_FACES THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]));;

(* Lean: code_256_ten_faces *)
let C977IF_CODE_256_TEN_FACES = prove
 (`forall c1 c2 a b l i. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = ccc977ri_family /\
     i < 12 /\ ownmask (c1 i) (c2 i) (a i) (b i) l = 256
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           c977if_pframe (a i) (b i) (a i * c1 i + b i * c2 i - l / &2)
                         (--b i * c1 i + a i * c2 i - l / &2) l c' s' u' v' a' /\
           ((s' <= c' /\ (c977if_tenuu c' s' u' v' a' \/ c977if_tenuv c' s' u' v' a')) \/
            (c' <= s' /\ (c977if_tenuu c' s' u' v' a' \/ c977if_tenlv c' s' u' v' a'))) /\
           (c' = s' ==> c977if_tenuu c' s' u' v' a')`,
  C977IF_CODE_TAC
   (CONJ_TAC THENL
     [MATCH_MP_TAC C977IF_MARKER_EIGHT_TEN_FACE_COVER THEN ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC C977IF_MARKER_EIGHT_TEN_FACES_EQ THEN
      ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]));;

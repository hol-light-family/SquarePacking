(* ========================================================================= *)
(* Port of source/S12/AffineOverlap.lean (Jatloe, N12-jatloe).               *)
(* Affine.const n a = aff_const n a (n zero coefficients), Affine.coord n i  *)
(* = aff_coord n i (the i-th unit vector of length n).  Points of Fin 2 and  *)
(* Fin 4 are the lists [x0;x1] and [x0;x1;x2;x3].  The AffineOverlap-       *)
(* Certificate structure is AffCert first second inputsA inputsB pointX      *)
(* pointY proofs; its subtype fields first/second are checked in            *)
(* affcert_check.                                                            *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/certlib/LinearImplication.ml";;
needs "n12/certlib/OverlapCertificate.ml";;

(* the unit coefficient vector of length n with 1 at position i *)
let lunitv = define
 `(lunitv 0 i = []) /\
  (lunitv (SUC n) i = if i = 0 then CONS (&1) (REPLICATE n (&0))
                      else CONS (&0) (lunitv n (i - 1)))`;;

(* Lean: Affine.const *)
let aff_const = new_definition `aff_const n a = Affine (REPLICATE n (&0)) a`;;
(* Lean: Affine.coord *)
let aff_coord = new_definition `aff_coord n i = Affine (lunitv n i) (&0)`;;
(* Lean: Affine.sub *)
let aff_sub = new_definition `aff_sub f g = aff_add f (aff_scale (-- &1) g)`;;

(* Lean: Affine.eval_const *)
let AO_AFF_EVAL_CONST = prove
 (`forall n a p. aff_eval (aff_const n a) p = a`,
  REWRITE_TAC[aff_const; aff_eval; LDOT_REPLICATE_0; REAL_ADD_LID]);;

let AO_LDOT_LUNIT = prove
 (`forall n i p. i < n /\ i < LENGTH p ==> ldot (lunitv n i) p = EL i p`,
  INDUCT_TAC THENL [REWRITE_TAC[LT]; ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; CONJUNCT1 LT] THEN
  POP_ASSUM(K ALL_TAC) THEN STRIP_TAC THEN
  REWRITE_TAC[lunitv] THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[ldot; EL; HD; LDOT_REPLICATE_0; REAL_MUL_LID; REAL_ADD_RID;
                  REAL_MUL_LZERO; REAL_ADD_LID] THEN
  SUBGOAL_THEN `i = SUC(i - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EL; TL; SUC_SUB1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* Lean: Affine.eval_coord *)
let AO_AFF_EVAL_COORD = prove
 (`forall n i p. i < n /\ i < LENGTH p ==> aff_eval (aff_coord n i) p = EL i p`,
  SIMP_TAC[aff_coord; aff_eval; AO_LDOT_LUNIT; REAL_ADD_RID]);;

(* Lean: Affine.eval_sub *)
let AO_AFF_EVAL_SUB = prove
 (`forall f g p. aff_eval (aff_sub f g) p = aff_eval f p - aff_eval g p`,
  REWRITE_TAC[aff_sub; LC_AFF_EVAL_ADD; LC_AFF_EVAL_SCALE] THEN REAL_ARITH_TAC);;

(* Lean: insideAffineForms *)
let inside_forms = new_definition
 `inside_forms n r cx cy px py =
    [LinCon (aff_add (aff_const n (rs_side r / &2))
       (aff_add (aff_scale (rs_c r) (aff_sub px cx)) (aff_scale (rs_s r) (aff_sub py cy)))) true;
     LinCon (aff_sub (aff_const n (rs_side r / &2))
       (aff_add (aff_scale (rs_c r) (aff_sub px cx)) (aff_scale (rs_s r) (aff_sub py cy)))) true;
     LinCon (aff_add (aff_const n (rs_side r / &2))
       (aff_add (aff_scale (--(rs_s r)) (aff_sub px cx)) (aff_scale (rs_c r) (aff_sub py cy)))) true;
     LinCon (aff_sub (aff_const n (rs_side r / &2))
       (aff_add (aff_scale (--(rs_s r)) (aff_sub px cx)) (aff_scale (rs_c r) (aff_sub py cy)))) true]`;;

let AO_INSIDE_FORMS_EXPAND = prove
 (`forall n r cx cy px py p.
     (forall f. MEM f (inside_forms n r cx cy px py) ==> lc_holds f p) <=>
     &0 < rs_side r / &2 + (rs_c r * (aff_eval px p - aff_eval cx p) +
                            rs_s r * (aff_eval py p - aff_eval cy p)) /\
     &0 < rs_side r / &2 - (rs_c r * (aff_eval px p - aff_eval cx p) +
                            rs_s r * (aff_eval py p - aff_eval cy p)) /\
     &0 < rs_side r / &2 + (--(rs_s r) * (aff_eval px p - aff_eval cx p) +
                            rs_c r * (aff_eval py p - aff_eval cy p)) /\
     &0 < rs_side r / &2 - (--(rs_s r) * (aff_eval px p - aff_eval cx p) +
                            rs_c r * (aff_eval py p - aff_eval cy p))`,
  REWRITE_TAC[inside_forms; MEM; FORALL_UNWIND_THM2;
    TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`; FORALL_AND_THM; NOT_IN_EMPTY] THEN
  REWRITE_TAC[lc_holds; LC_AFF_EVAL_ADD; AO_AFF_EVAL_SUB; LC_AFF_EVAL_SCALE;
              AO_AFF_EVAL_CONST]);;

(* Lean: insideAffineForms_sound *)
let AO_INSIDE_FORMS_SOUND = prove
 (`forall n r cx cy px py p.
     rs_check r /\ (forall f. MEM f (inside_forms n r cx cy px py) ==> lc_holds f p)
     ==> (aff_eval px p - aff_eval cx p, aff_eval py p - aff_eval cy p) IN rs_sqset r`,
  REWRITE_TAC[AO_INSIDE_FORMS_EXPAND; rs_sqset; IN_SQSET; linside] THEN
  REPEAT GEN_TAC THEN REAL_ARITH_TAC);;

(* Lean: insideAffineForms_iff *)
let AO_INSIDE_FORMS_IFF = prove
 (`forall n r cx cy px py p.
     (forall f. MEM f (inside_forms n r cx cy px py) ==> lc_holds f p) <=>
     abs(rs_c r * (aff_eval px p - aff_eval cx p) + rs_s r * (aff_eval py p - aff_eval cy p))
       < rs_side r / &2 /\
     abs(--(rs_s r) * (aff_eval px p - aff_eval cx p) + rs_c r * (aff_eval py p - aff_eval cy p))
       < rs_side r / &2`,
  REWRITE_TAC[AO_INSIDE_FORMS_EXPAND] THEN REAL_ARITH_TAC);;

(* coefficient i of an affine form (0 beyond its length) *)
let lcoeff = new_definition
 `lcoeff (cs:real list) i = if i < LENGTH cs then EL i cs else &0`;;

(* Lean: Affine.liftLeft / Affine.liftRight (Affine 2 -> Affine 4) *)
let aff_liftl = define
 `aff_liftl (Affine cs k) = Affine [lcoeff cs 0; lcoeff cs 1; &0; &0] k`;;
let aff_liftr = define
 `aff_liftr (Affine cs k) = Affine [&0; &0; lcoeff cs 0; lcoeff cs 1] k`;;
(* Lean: LinearConstraint.liftLeft / liftRight *)
let lc_liftl = define `lc_liftl (LinCon f b) = LinCon (aff_liftl f) b`;;
let lc_liftr = define `lc_liftr (LinCon f b) = LinCon (aff_liftr f) b`;;

let AO_LDOT_2 = prove
 (`forall cs x0 x1. ldot cs [x0; x1] = lcoeff cs 0 * x0 + lcoeff cs 1 * x1`,
  GEN_TAC THEN STRUCT_CASES_TAC(ISPEC `cs:real list` list_CASES) THEN
  REWRITE_TAC[ldot; lcoeff; LENGTH; LT_REFL; CONJUNCT1 LT] THEN
  REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_LID] THEN
  STRUCT_CASES_TAC(ISPEC `t:real list` list_CASES) THEN
  REWRITE_TAC[ldot; LENGTH; LDOT_NIL_RIGHT; ONE; EL; HD; TL; LT_SUC; LT_0] THEN
  REWRITE_TAC[CONJUNCT1 LT; LT_REFL] THEN REAL_ARITH_TAC);;

(* Lean: Affine.eval_liftLeft *)
let AO_AFF_EVAL_LIFTLEFT = prove
 (`forall f x0 x1 x2 x3. aff_eval (aff_liftl f) [x0; x1; x2; x3] = aff_eval f [x0; x1]`,
  MATCH_MP_TAC affine_INDUCT THEN
  REWRITE_TAC[aff_liftl; aff_eval; ldot; AO_LDOT_2] THEN REAL_ARITH_TAC);;

(* Lean: Affine.eval_liftRight *)
let AO_AFF_EVAL_LIFTRIGHT = prove
 (`forall f x0 x1 x2 x3. aff_eval (aff_liftr f) [x0; x1; x2; x3] = aff_eval f [x2; x3]`,
  MATCH_MP_TAC affine_INDUCT THEN
  REWRITE_TAC[aff_liftr; aff_eval; ldot; AO_LDOT_2] THEN REAL_ARITH_TAC);;

(* Lean: LinearConstraint.holds_liftLeft *)
let AO_HOLDS_LIFTLEFT = prove
 (`forall f x0 x1 x2 x3. lc_holds (lc_liftl f) [x0; x1; x2; x3] <=> lc_holds f [x0; x1]`,
  MATCH_MP_TAC lincon_INDUCT THEN
  REWRITE_TAC[lc_liftl; lc_holds; AO_AFF_EVAL_LIFTLEFT]);;

(* Lean: LinearConstraint.holds_liftRight *)
let AO_HOLDS_LIFTRIGHT = prove
 (`forall f x0 x1 x2 x3. lc_holds (lc_liftr f) [x0; x1; x2; x3] <=> lc_holds f [x2; x3]`,
  MATCH_MP_TAC lincon_INDUCT THEN
  REWRITE_TAC[lc_liftr; lc_holds; AO_AFF_EVAL_LIFTRIGHT]);;

(* Lean: structure AffineOverlapCertificate *)
let affcert_INDUCT,affcert_RECURSION = define_type
 "affcert = AffCert refsq refsq (lincon list) (lincon list) affine affine
                    (((real#lincon)list)list)";;
let ac_first = define `ac_first (AffCert f s ia ib px py pr) = f`;;
let ac_second = define `ac_second (AffCert f s ia ib px py pr) = s`;;
let ac_inputsA = define `ac_inputsA (AffCert f s ia ib px py pr) = ia`;;
let ac_inputsB = define `ac_inputsB (AffCert f s ia ib px py pr) = ib`;;
let ac_pointX = define `ac_pointX (AffCert f s ia ib px py pr) = px`;;
let ac_pointY = define `ac_pointY (AffCert f s ia ib px py pr) = py`;;
let ac_proofs = define `ac_proofs (AffCert f s ia ib px py pr) = pr`;;

(* Lean: AffineOverlapCertificate.inputs *)
let ac_inputs = new_definition
 `ac_inputs w = APPEND (MAP lc_liftl (ac_inputsA w)) (MAP lc_liftr (ac_inputsB w))`;;

(* Lean: AffineOverlapCertificate.targets *)
let ac_targets = new_definition
 `ac_targets w =
    APPEND (inside_forms 4 (ac_first w) (aff_coord 4 0) (aff_coord 4 1) (ac_pointX w) (ac_pointY w))
           (inside_forms 4 (ac_second w) (aff_coord 4 2) (aff_coord 4 3) (ac_pointX w) (ac_pointY w))`;;

(* Lean: AffineOverlapCertificate.Check, with the subtype checks of first, second *)
let affcert_check = new_definition
 `affcert_check w <=>
    rs_check (ac_first w) /\ rs_check (ac_second w) /\
    forall target. MEM target (ac_targets w) ==>
      exists terms. MEM terms (ac_proofs w) /\ limp_check 4 (ac_inputs w) target terms`;;

let AO_INPUTS_HOLD = prove
 (`forall ia ib x0 x1 x2 x3.
     (forall f. MEM f ia ==> lc_holds f [x0; x1]) /\ (forall f. MEM f ib ==> lc_holds f [x2; x3])
     ==> forall f. MEM f (APPEND (MAP lc_liftl ia) (MAP lc_liftr ib)) ==> lc_holds f [x0; x1; x2; x3]`,
  REWRITE_TAC[MEM_APPEND; MEM_MAP] THEN REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[AO_HOLDS_LIFTLEFT; AO_HOLDS_LIFTRIGHT]);;

let AO_EL4 = prove
 (`forall x0 x1 x2 x3:real. EL 0 [x0; x1; x2; x3] = x0 /\ EL 1 [x0; x1; x2; x3] = x1 /\
                      EL 2 [x0; x1; x2; x3] = x2 /\ EL 3 [x0; x1; x2; x3] = x3`,
  REWRITE_TAC[EL; HD; TL; num_CONV `3`; num_CONV `2`; num_CONV `1`]);;

let AO_COORD4 = prove
 (`forall x0 x1 x2 x3.
     aff_eval (aff_coord 4 0) [x0; x1; x2; x3] = x0 /\
     aff_eval (aff_coord 4 1) [x0; x1; x2; x3] = x1 /\
     aff_eval (aff_coord 4 2) [x0; x1; x2; x3] = x2 /\
     aff_eval (aff_coord 4 3) [x0; x1; x2; x3] = x3`,
  SIMP_TAC[AO_AFF_EVAL_COORD; LENGTH; ARITH; AO_EL4]);;

(* Lean: AffineOverlapCertificate.sound *)
let AO_SOUND = prove
 (`forall w x0 x1 x2 x3.
     affcert_check w /\
     (forall f. MEM f (ac_inputsA w) ==> lc_holds f [x0; x1]) /\
     (forall f. MEM f (ac_inputsB w) ==> lc_holds f [x2; x3])
     ==> overlaps_at (rs_sqset (ac_first w)) (rs_sqset (ac_second w)) (x0,x1) (x2,x3)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[affcert_check] THEN STRIP_TAC THEN
  SUBGOAL_THEN `forall f. MEM f (ac_inputs w) ==> lc_holds f [x0; x1; x2; x3]` ASSUME_TAC THENL
   [REWRITE_TAC[ac_inputs] THEN MATCH_MP_TAC AO_INPUTS_HOLD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `forall f. MEM f (ac_targets w) ==> lc_holds f [x0; x1; x2; x3]` MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `f:lincon` o check (fun th ->
      can (find_term ((=) `ac_proofs:affcert->((real#lincon)list)list`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC LI_LINEAR_IMPLICATION_SOUND THEN
    MAP_EVERY EXISTS_TAC [`4`; `ac_inputs w`; `terms:(real#lincon)list`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ac_targets; MEM_APPEND; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[overlaps_at] THEN
  EXISTS_TAC `(aff_eval (ac_pointX w) [x0; x1; x2; x3], aff_eval (ac_pointY w) [x0; x1; x2; x3])` THEN
  REWRITE_TAC[psub; FST; SND] THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`4`; `ac_first w`; `aff_coord 4 0`; `aff_coord 4 1`; `ac_pointX w`;
                  `ac_pointY w`; `[x0; x1; x2; x3]:real list`] AO_INSIDE_FORMS_SOUND);
    MP_TAC(SPECL [`4`; `ac_second w`; `aff_coord 4 2`; `aff_coord 4 3`; `ac_pointX w`;
                  `ac_pointY w`; `[x0; x1; x2; x3]:real list`] AO_INSIDE_FORMS_SOUND)] THEN
  ASM_REWRITE_TAC[AO_COORD4]);;

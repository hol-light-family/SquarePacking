(* ========================================================================= *)
(* Port of Compact/Completion/OtherCases/WallProfile/VertexGeometry.lean     *)
(* (N12Compact.Completion.OtherCases.WallProfile).  Closed vertices, segment *)
(* interiors and wall limits.  Lean `upper`/`lower`/`supportRadius` are      *)
(* ABT_upper / ABT_lower / tss_support_radius.                               *)
(* ========================================================================= *)

needs "n12/geometry/p2_base.ml";;
needs "n12/geometry/CP_OtherCases_WallProfile_SupportGeometry.ml";;
needs "n12/geometry/CentralEscapeSegment.ml";;
needs "n12/geometry/SectionCapacity.ml";;

(* Lean: vertex *)
let OCWPVG_VERTEX = prove
 (`forall c s u v a U V.
      c * c + s * s = &1 /\ u <= U /\ U <= u + a /\ v <= V /\ V <= v + a
      ==> lclosed c s u v a (c * U - s * V) (s * U + c * V)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[lclosed] THEN
  SUBGOAL_THEN `c * (c * U - s * V) + s * (s * U + c * V) = U /\
                --s * (c * U - s * V) + c * (s * U + c * V) = V`
    (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
    ASM_REWRITE_TAC[]]);;

(* Lean: strict_closed_segment *)
let OCWPVG_STRICT_CLOSED_SEGMENT = prove
 (`forall c s u v a x y x' y' t.
      lclosed c s u v a x y /\ linside c s u v a x' y' /\ &0 < t /\ t < &1
      ==> linside c s u v a ((&1 - t) * x + t * x') ((&1 - t) * y + t * y')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lclosed; linside] THEN STRIP_TAC THEN
  NLIN_FACTS_TAC []
   [`&0 <= (&1 - t) * ((c * x + s * y) - u)`;
    `&0 < t * ((c * x' + s * y') - u)`;
    `&0 <= (&1 - t) * ((u + a) - (c * x + s * y))`;
    `&0 < t * ((u + a) - (c * x' + s * y'))`;
    `&0 <= (&1 - t) * ((--s * x + c * y) - v)`;
    `&0 < t * ((--s * x' + c * y') - v)`;
    `&0 <= (&1 - t) * ((v + a) - (--s * x + c * y))`;
    `&0 < t * ((v + a) - (--s * x' + c * y'))`] THEN
  REPEAT CONJ_TAC THEN NLIN_TAC ~deg2:false []);;

(* Lean: vertical_owned *)
let OCWPVG_VERTICAL_OWNED = prove
 (`forall c s u v a x b h.
      b < h /\ linside c s u v a x b /\ linside c s u v a x h
      ==> forall y. b <= y ==> y <= h ==> linside c s u v a x y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `y:real` THEN REPEAT DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`;
                `x:real`; `b:real`; `x:real`; `h:real`; `(y - b) / (h - b)`]
    CES_INSIDE_SEGMENT) THEN
  SUBGOAL_THEN `&0 < h - b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(y - b) / (h - b) * (h - b) = y - b` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `T0 = (y - b) / (h - b)` THEN
  SUBGOAL_THEN `(&1 - T0) * x + T0 * x = x /\ (&1 - T0) * b + T0 * h = y`
    (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC `T0 * (h - b) = y - b` THEN REAL_ARITH_TAC);;

(* Lean: lower_wall_vertex *)
let OCWPVG_LOWER_WALL_VERTEX = prove
 (`forall c s u v a.
      c * c + s * s = &1 /\ &0 < a /\
      (forall x y. linside c s u v a x y ==> &0 <= y)
      ==> &0 <= s * (u + a) + c * v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC SCAP_AFFINE_ENDPOINT_NONNEG THEN
  MAP_EVERY EXISTS_TAC [`a:real`; `c - s`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`c * (u + a - t) - s * (v + t)`; `s * (u + a - t) + c * (v + t)`]) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[linside] THEN
    SUBGOAL_THEN
     `c * (c * (u + a - t) - s * (v + t)) + s * (s * (u + a - t) + c * (v + t)) =
      u + a - t /\
      --s * (c * (u + a - t) - s * (v + t)) + c * (s * (u + a - t) + c * (v + t)) =
      v + t` (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN UNDISCH_TAC `c * c + s * s = &1` THEN CONV_TAC REAL_RING;
      ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

(* Lean: radius_even *)
let OCWPVG_RADIUS_EVEN = prove
 (`forall c s a nx ny. tss_support_radius c s a (--nx) (--ny) = tss_support_radius c s a nx ny`,
  REWRITE_TAC[tss_support_radius] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[REAL_ARITH `--nx * c + --ny * s = --(nx * c + ny * s)`;
              REAL_ARITH `-- --nx * s + --ny * c = --(--nx * s + ny * c)`; REAL_ABS_NEG]);;

(* Lean: upper_neg *)
let OCWPVG_UPPER_NEG = prove
 (`forall c s u v a nx ny.
      ABT_upper c s u v a (--nx) (--ny) = --ABT_lower c s u v a nx ny`,
  REWRITE_TAC[ABT_upper; ABT_lower; OCWPVG_RADIUS_EVEN] THEN REAL_ARITH_TAC);;

(* Lean: lower_neg *)
let OCWPVG_LOWER_NEG = prove
 (`forall c s u v a nx ny.
      ABT_lower c s u v a (--nx) (--ny) = --ABT_upper c s u v a nx ny`,
  REWRITE_TAC[ABT_upper; ABT_lower; OCWPVG_RADIUS_EVEN] THEN REAL_ARITH_TAC);;

(* Lean: negative_frame *)
let OCWPVG_NEGATIVE_FRAME = prove
 (`forall c s u v a. c * c + s * s = &1 /\ &0 < a
     ==> exists c' s' u' v' a'. c' * c' + s' * s' = &1 /\ &0 < a' /\
           &0 < c' /\ s' <= &0 /\ a' = a /\
           (forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`c:real`; `s:real`; `u:real`; `v:real`; `a:real`] OCWPSG_POSITIVE_FRAME) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `s1 = &0` THENL
   [MAP_EVERY EXISTS_TAC [`c1:real`; `s1:real`; `u1:real`; `v1:real`; `a1:real`] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL];
    MAP_EVERY EXISTS_TAC [`s1:real`; `--c1`; `--v1 - a1`; `u1:real`; `a1:real`] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
      can (find_term ((=) `linside`)) (concl th) then
      REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[linside] THEN REPEAT CONJ_TAC THEN TRY(REPEAT GEN_TAC) THEN
    ASM_REAL_ARITH_TAC]);;

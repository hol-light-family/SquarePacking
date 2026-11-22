# n12/certlib — the S12 pose-semantics layer in HOL Light

Port of Jatloe et al.'s `source/S12` "pose semantics" (Lean:
`n12/ext/jatloe/Lean/Proofs/N12-jatloe/source/S12/`). The certificate-based cases are
stated against these definitions. Every file is named after its Lean module.
Each file starts with `needs "n12/geometry/p2_base.ml";;` and needs its dependencies.
`n12/certlib/p3_all.ml` loads everything. After `p2_base.ml` this takes 85 s, including the few geometry
files it needs; about 40 s of that is checking the 192 angle enclosures.
No `CHEAT_TAC`, `new_axiom` or `mk_thm` is used.

Load order (each file needs the files above it):

QuadraticInterval, AngleEnclosure, Convex, ConvexOverlap, OverlapCertificate,
ReferenceGeometry, AngleReference, PoseBounds, Diameter, SquareSupportBase, AxisAlgebra,
AxisGap, ScalarSATGeneral, SquareAxes, LinearCertificate, LinearImplication, AffineOverlap,
AxisOverlapCertificate, RegionTree, PoseRegion, IntervalCoverage, OwnerEnclosure,
ContinuousPruning, DomainRelaxation, ContinuousCertificate, OrientedCoverage, AngleData64,
AngleData128, Angles192.

## Representation choices

These choices apply to every file.

- **Squares.** A Lean `OpenSquare q` is the 5-tuple `c s u v a`
  (`q.c q.s q.loU q.loV q.side`).
  - `q.Inside x y` is `linside c s u v a x y`, and `InsideContainer q` is `lcont c s u v a`.
  - `centerX q` and `centerY q` are `lcx c s u v a` and `lcy c s u v a`.
  - `∀ x y, ¬(q.Inside x y ∧ r.Inside x y)` is `ldisj cq sq uq vq aq cr sr ur vr ar`.
  - Lean's structure invariants become explicit hypotheses in every theorem that has a
    square: `c * c + s * s = &1 /\ &0 < a`.
  - A family `q : Fin n → OpenSquare` is five functions `cq sq uq vq aq : num->real`, indexed
    by `i < n`, as in `NPACK`.
- **Points.** Points of `ℝ × ℝ` are HOL pairs `real#real`.
  - `P - A` is `psub P A`.
  - `squareSet q` is `sqset c s u v a`, a set of pairs (`IN_SQSET`).
  - `ratPoint` is the identity.
- **Rationals.** Lean `ℚ` data and casts are HOL reals. The concrete data are rational
  literals `&p / &q`.
- **Lean structures.**
  - They become HOL types made by `define_type`, with accessor functions. Example: `AngleEnc`
    with accessors `ae_lower`, `ae_upper`, …
  - A field of subtype type `{w // w.Check}` is stored as the plain value. Its proof becomes a
    conjunct of the HOL check predicate of the containing structure.
  - Lists of subtypes become plain lists, together with an explicit hypothesis
    `forall w. MEM w l ==> ..._check w`.
  - Structures whose fields are proofs (`PosePruning.checked`, `LeafRelaxation`,
    `DomainRelaxation`, …) become data plus an `_ok` predicate.
- **Affine forms and rows.**
  - `Affine n` is `Affine (coeffs:real list) (const:real)`.
  - `LinearConstraint n` is `LinCon (f:affine) (strict:bool)`.
  - A point `x : Fin n → ℝ` is a `real list`, with `x i = EL i x`. A 2-D pose row is checked
    at `[lcx c s u v a; lcy c s u v a]`, and a 4-D row at `[x0; x1; x2; x3]`.
  - `aff_eval (Affine cs k) x = ldot cs x + k`. `ldot` stops at the shorter list.
  - `aff_add` pads with zeros.
  - `aff_const n a`, `aff_coord n i` and `aff_zero n` have exactly `n` coefficients, as in
    Lean.
  - `liftLeft` and `liftRight` produce exactly 4 coefficients. They use `lcoeff cs i`
    (= 0 past the end).
  - The soundness theorems hold for all lists, so this is at least as strong as Lean's.
- **Lists.** `List.flatMap f l` is `lflat (MAP f l)` (`MEM_LFLAT`). HOL Light has no `FLAT`.
  `Fin`-indexed families of plans are lists:
  - `DomainPruning.plans i` is `EL i plans`, paired with `sources` by `ALL2`.
  - `DomainRelaxation.destination` is `dest : num->num`.

## Key definitions (HOL statements)

**Angle enclosures** (`AngleEnclosure.ml`, `QuadraticInterval.ml`)

```
quad_check_on (Quadratic a b c) l h <=>
   l < h /\ &0 <= quad_eval (Quadratic a b c) l /\
   &0 <= quad_eval (Quadratic a b c) l + (h - l) * (&2 * a * l + b) / &2 /\
   &0 <= quad_eval (Quadratic a b c) h            (quad_eval (Quadratic a b c) t = a*t pow 2+b*t+c)
normalC t = (&1 - t pow 2) / (&1 + t pow 2);   normalS t = (&2 * t) / (&1 + t pow 2)
support_quad u v out d e = Quadratic (out + (d*u - e*v)) (--(&2) * (d*v + e*u)) (out - (d*u - e*v))
wall_quad wl = Quadratic (-- &1 - wl) (&2) (&1 - wl)
angle_enc = AngleEnc lower upper c s outer inner wall
ae_check w <=> &0 <= ae_lower w /\ ae_upper w <= &1 /\ ae_c w pow 2 + ae_s w pow 2 = &1 /\
   &0 < ae_outer w /\ &0 < ae_inner w /\ ae_inner w * ae_outer w <= &1 /\
   quad_check_on (support_quad (ae_c w) (ae_s w) (ae_outer w) (&1) (&1)) (ae_lower w) (ae_upper w) /\
   ... (the same for the sign pairs (1,-1), (-1,1), (-1,-1)) /\
   quad_check_on (wall_quad (ae_wall w)) (ae_lower w) (ae_upper w)
ae_reference w lowerSide = RefSq (ae_c w) (ae_s w) (lowerSide * ae_inner w)
```

**Reference squares** (`OverlapCertificate.ml`)

- `refsq = RefSq c s side`, with `rs_check r <=> rs_c r pow 2 + rs_s r pow 2 = &1 /\ &0 < rs_side r`.
- `r.toSquare` is the square `(c, s, --side/2, --side/2, side)`. Its point set is
  `rs_sqset r = sqset (rs_c r) (rs_s r) (--(rs_side r) / &2) (--(rs_side r) / &2) (rs_side r)`.
- `overlaps_at S1 S2 A B <=> exists P. psub P A IN S1 /\ psub P B IN S2`. This is `OverlapsAt`, on
  the square sets.

**Pose leaves** (`OwnerEnclosure.ml`, `OrientedCoverage.ml`, `ContinuousPruning.ml`)

```
pose_leaf = PoseLeaf (angle:angle_enc) (inputs:lincon list)       accessors pl_angle, pl_inputs
pose_realizes leaf c s u v a <=>
   (forall f. MEM f (pl_inputs leaf) ==> lc_holds f [lcx c s u v a; lcy c s u v a]) /\
   (forall P. psub P (lcx c s u v a, lcy c s u v a) IN rs_sqset (ae_reference (pl_angle leaf) (&1))
        ==> P IN sqset c s u v a)
angle_witness leaf c s u v a <=>
   exists c' s' u' v' a' t. c' * c' + s' * s' = &1 /\ &0 < a' /\ c' = normalC t /\ s' = normalS t /\
     ae_lower (pl_angle leaf) <= t /\ t <= ae_upper (pl_angle leaf) /\ a' = a /\
     lcx c' s' u' v' a' = lcx c s u v a /\ lcy c' s' u' v' a' = lcy c s u v a /\
     forall x y. linside c' s' u' v' a' x y <=> linside c s u v a x y
oriented_realizes leaf c s u v a <=> pose_realizes leaf c s u v a /\ angle_witness leaf c s u v a
oriented_pose_covered leaves c s u v a <=> exists l. MEM l leaves /\ oriented_realizes l c s u v a
pose_covered domain c s u v a <=> exists l. MEM l domain /\ pose_realizes l c s u v a
```

**Rows** (`LinearCertificate.ml`, `LinearImplication.ml`, `AffineOverlap.ml`)

```
lc_holds (LinCon f b) x <=> if b then &0 < aff_eval f x else &0 <= aff_eval f x
lc_opposite (LinCon f b) = LinCon (aff_scale (-- &1) f) (~b)
lin_comb n [] = lc_zero n;  lin_comb n (CONS t ts) = lc_add (lc_scale (FST t) (SND t)) (lin_comb n ts)
lcert_check n inputs terms <=> (forall t. MEM t terms ==> &0 <= FST t /\ MEM (SND t) inputs) /\
   lc_strict (lin_comb n terms) = true /\ lc_form (lin_comb n terms) = aff_zero n
limp_check n inputs target terms <=> lcert_check n (CONS (lc_opposite target) inputs) terms
inside_forms n r cx cy px py = the 4 strict rows side/2 +- (c*(px-cx)+s*(py-cy)),
                                side/2 +- (--s*(px-cx)+c*(py-cy))
```

**Pose inputs** (`PoseRegion.ml`)

```
outer_ref w = RefSq (ae_c w) (ae_s w) ((&1001 / &1000) * ae_outer w)
point_forms r P = inside_forms 2 r (aff_coord 2 0) (aff_coord 2 1) (aff_const 2 (FST P)) (aff_const 2 (SND P))
wall_forms w = [x - wall/2 >= 0; (4 - wall/2) - x >= 0; y - wall/2 >= 0; (4 - wall/2) - y >= 0]
pose_inputs w inside = APPEND (APPEND (lflat (MAP (point_forms (outer_ref w)) inside)) (wall_forms w))
                              [LinCon (aff_const 2 (&1)) T]
pose_forbidden w outside = MAP (point_forms (ae_reference w (&1))) outside
```

**Angle data** (`AngleData64.ml`, `AngleData128.ml`, `Angles192.ml`)

- `n12/scripts/angle_extract.py` generates the two data files from the Lean sources.
- `angles64` and `angles128` are lists of `AngleEnc` literals, in Lean's order. The OCaml
  arrays `angle64_tm` / `angle128_tm` hold the terms.
- `ANGLE64_CHECKED.(k)` / `ANGLE128_CHECKED.(k)` are `|- ae_check (AngleEnc ...)` (Lean
  `angle64_k_checked`). They are proved by `AE_CHECK_RULE`: rewriting followed by
  `REAL_RAT_REDUCE_CONV`.
- `ANGLES64_CHECKED : forall k. k < 64 ==> ae_check (EL k angles64)` (and the same for 128).
- `AD64_EL` and `AD128_EL` give `EL k angles64 = <literal>` for every k.
- `ANGLES64_COVER : covers_interval (&0) (&1) angles64` (and the same for 128) are Lean's
  `angles64_cover` and `angles128_cover`.
- `s12_angles i = if i < 64 then EL i angles64 else EL (i - 64) angles128` is Lean's
  `C713Shared.angles`. `S12_ANGLES_CHECKED : forall i. i < 192 ==> ae_check (s12_angles i)`.

## Definitions and theorems with their Lean counterparts

Every HOL item has a `(* Lean: ... *)` comment above it in the source. The main ones are
listed here.

| HOL | Lean |
|---|---|
| `QI_QUADRATIC_SOUND` | `Quadratic.sound` |
| `AE_NORMAL_UNIT`, `AE_NORMAL_NONNEGATIVE` | `normal_unit`, `normal_nonnegative` |
| `AE_SUPPORT_QUADRATIC_SOUND`, `AE_SUPPORT`, `AE_WALL_BOUND` | `supportQuadratic_sound`, `AngleEnclosure.support`, `.wall_bound` |
| `AE_FIRST_QUADRANT_RATIONAL` | `first_quadrant_rational` (WallNormalBounds) |
| `AE_CHECK_RULE` (OCaml) | `decide +kernel` for `AngleEnclosure.Check` |
| `CVX_INTERVAL_SEGMENT`, `CVX_INSIDE_SEGMENT` (= `CES_INSIDE_SEGMENT`), `tri_cert_check`, `CVX_TRIANGLE_CERTIFICATE_SOUND` | Convex |
| `DIA_INSIDE_DISTANCE_BOUND`, `DIA_NORMALIZED_DIAMETER_BOUND`, `owns` | Diameter |
| `sqset`, `pconvex`, `pconvex_hull`, `overlaps_at`, `CO_SQUARESET_CONVEX`, `CO_OVERLAPSAT_SYMM`, `CO_OVERLAPSAT_CONVEX_LEFT/RIGHT`, `CO_VERTEX_OVERLAP_EXTENDS` | ConvexOverlap (`convexHull` → `pconvex_hull`, via Multivariate `convex hull` on `real^2`) |
| `refsq`, `rs_check`, `rs_sqset`, `rs_inside_at`, `OC_INSIDEAT_SOUND`, `ovcert`, `ovcert_check`, `vertex_hull`, `OC_SOUND`, `OC_EXCLUDES` | OverlapCertificate |
| `RG_STRICT_ABS_LINEAR_BOUND`, `RG_NORMAL_CHANGE_INNER`, `RG_REFERENCE_INNER_CONTAINMENT` | ReferenceGeometry |
| `ae_reference`, `AR_REFERENCE_CHECKED`, `AR_INNER_SOUND` | `AngleEnclosure.reference`, `.reference_checked`, **`.inner_sound`** |
| `PB_POSITIVE_FRAME_ALL_WALLS`, `PB_OUTER_SOUND`, `PB_WALL_SOUND` | `positive_frame_all_walls`, **`AngleEnclosure.outer_sound`**, **`.wall_sound`** |
| `SSB_*`, `signedOne` (`squareRadius` = `tss_support_radius`) | SquareSupportBase (`SSB_INSIDE_CENTERED` = SquareFrame `inside_centered_iff`) |
| `planeL1`, `axis_overlap`, `AXA_WEIGHTED_TWO_LT`, `AXA_POSITIVE_NORMAL_GAP` | AxisAlgebra |
| `AXG_QUADRANT_COVER`, `normal_gap`, `axis_overlap_abs`, `AXG_AXIS_NORMAL_GAP`, `AXG_FOUR_AXES_ALGEBRA`, … | AxisGap |
| `ssg_overlap`, `SSG_*`, `SSG_OVERLAP` | Compact/Geometry/ScalarSATGeneral (`N12Compact.SATGeneral`). This is a Compact module, ported here because SquareAxes needs it and geometry/ had no port. |
| `relC`, `relS`, `axis_separates`, `SAX_*`, `SAX_SQUARE_SEPARATING_AXES` | SquareAxes |
| `affine`, `lincon`, `aff_eval`, `lc_holds`, `lin_comb`, `lcert_check`, `LC_LINEAR_CERTIFICATE_SOUND` | LinearCertificate |
| `lc_opposite`, `LI_OPPOSITE_HOLDS`, `limp_check`, `LI_LINEAR_IMPLICATION_SOUND` | LinearImplication |
| `aff_const`, `aff_coord`, `aff_sub`, `inside_forms`, `AO_INSIDE_FORMS_SOUND/IFF`, `aff_liftl/r`, `lc_liftl/r`, `affcert`, `affcert_check`, `AO_SOUND` | AffineOverlap |
| `rs_rat_radius`, `rs_at_u/v` (atCenter), `pair_axes`, `axis_gap_form`, `axis_overlap_forms`, `AOC_AXISOVERLAPFORMS_SOUND`, `axcert`, `axcert_check`, `AOC_SOUND` | AxisOverlapCertificate |
| `rtree` (`RLeaf`/`REmpty`/`RCut`/`RForbidden`), `rtree_check inputs forbidden tree`, `rtree_leaves inputs tree`, `RT_SOUND` | RegionTree |
| `outer_ref`, `point_forms`, `wall_forms`, **`pose_inputs`**, **`pose_forbidden`**, `PR_POSEINPUTS_SOUND`, `PR_POSEFORBIDDEN_SOUND`, `pose_root`, `proot_check`, `PR_POSEROOT_SOUND` | PoseRegion |
| `covers_interval`, `IC_COVERSINTERVAL_SOUND` | IntervalCoverage |
| **`pose_leaf`**, **`pose_realizes`**, `proot_leaves`, `owner_enc`, `oe_check`, `oe_leaves`, `OE_SOUND`, `owner_pair`, `op_check`, `OE_OWNERPAIR_SOUND` | OwnerEnclosure (`OE_SOUND_WITNESS` is the common core of `.sound` and `.oriented_sound`) |
| `prune_block`, `pb_check`, `pose_covered`, `CPR_PRUNEBLOCK_SOUND`, `pose_pruning`, `pp_ok`, `pp_result`, `CPR_POSEPRUNING_SOUND`, `dp_ok`, `dp_result`, `CPR_DOMAINPRUNING_SOUND`, `cps_ok`, `cps_result`, `CPR_CONTINUOUSPRUNESTEP_SOUND` | ContinuousPruning |
| `lr_ok`, `DR_LEAFRELAXATION_SOUND`, `dr_ok`, `DR_DOMAINRELAXATION_SOUND` | DomainRelaxation |
| `rlink`, `rl_check`, `CC_RELAXATIONLINK_SOUND`, `relaxation_cover_check`, `CC_RELAXATION_COVER_SOUND`, `cert_pruning`, `cpp_ok`, `CC_CERTIFIEDPOSEPRUNING_SOUND`, `pruning_cover_check`, `CC_PRUNING_COVER_SOUND` | ContinuousCertificate |
| **`angle_witness`**, **`oriented_realizes`**, **`oriented_pose_covered`**, `OCV_ORIENTED_COVERAGE_FORGET`, `OCV_OWNERENCLOSURE_ORIENTED_SOUND`, `rl_angle_check`, `OCV_RELAXATIONLINK_ORIENTED_SOUND`, `OCV_ORIENTED_RELAXATION_COVER_SOUND`, `OCV_POSEPRUNING_ORIENTED_SOUND`, `OCV_CERTIFIEDPOSEPRUNING_ORIENTED_SOUND`, `OCV_ORIENTED_PRUNING_COVER_SOUND` | OrientedCoverage |
| `OCV_POSE_TRANSFER`, `OCV_ORIENTED_TRANSFER` | the dictionary-free content of `IndexedRelaxation.Dictionary.transfer` (same angle, target rows hold at the centre) |

## Reused (not re-ported) geometry

| Lean | HOL |
|---|---|
| `exists_positive_frame` | `WCB_EXISTS_POSITIVE_FRAME` (geometry/WallCenterBarrier.ml) |
| `positive_frame_wall_bounds` | `TSS_POSITIVE_FRAME_WALL_BOUNDS` (geometry/ThreeSquareSupport.ml) |
| `affine_endpoint_nonnegative` | `SCAP_AFFINE_ENDPOINT_NONNEG` (geometry/SectionCapacity.ml) |
| `inside_iff_rotated_box` (face-coordinate direction) | `TSS_INSIDE_FACE` |
| `inside_segment` | `CES_INSIDE_SEGMENT` (geometry/CentralEscapeSegment.ml) |
| `between_three` / `between_four` | `SSI_BETWEEN_THREE` / `SSI_BETWEEN_FOUR` (geometry/ScalarSATIntervals.ml) |
| `squareRadius` | `tss_support_radius` (geometry/ThreeSquareSupport.ml) |
| `marker`, `marker_nonavoidance` (Markers, MarkerCoverGeometry) | Phase-1 `marker`, `MARKER_NONAVOID` (n12/phase1/markers.ml; centred `osq` form). The Lean `PoseBounds` imports MarkerCoverGeometry but uses none of its theorems. |

## Not ported, and why

- Lean `Decidable` instances. They are replaced by `AE_CHECK_RULE` and by rewriting followed by
  rational arithmetic.
- `CornerCover` (imported by ReferenceGeometry but unused there).
- `Markers.groupList`, `DiameterOK` and `markerCompatible`. They are pure data for the Phase-1
  marker groups, which already exist in HOL.
- `AngleData32` (not requested; no consumer among the 117 cases uses it).
- The remaining theorems of `WallNormalBounds` (`normal_bound_*`), which no file here uses.

# Comparison with the Lean proof

The HOL Light proof of s(12) = 4 is a port of the Lean 4 development by Jatloe, Gurevitch, Lewis
and Ahmed:
- repository [Queuingtheorydotcom/Jatloe12SquaresFormalized](https://github.com/Queuingtheorydotcom/Jatloe12SquaresFormalized),
  commit d0caf45;
- Lean root `Lean/Proofs/N12-jatloe/`;
- main theorem `N12Compact.Final.optimality : S12.packingConstant12 = 4` in
  `Compact/Assembly/Final.lean`.

This document covers four things: how the HOL statement relates to the Lean statement, how the
two developments correspond, where the HOL statements differ from the Lean ones, and what the
port showed about the Lean sources.  `jatloe_cert_map.md` describes the architecture of the Lean
development in detail; `audit.md` is an independent audit of the port.

## 1. The statements

| | Lean | HOL Light |
|---|---|---|
| theorem | `S12.packingConstant12 = 4` | `square_packing_side 12 = &4` and `forall t. packs 12 t <=> &4 <= t` |
| definition | `packingConstant12 = sInf {L \| 0 < L ∧ Nonempty (UnitPacking L)}` (`source/S12/PackingConstant.lean`) | `square_packing_side n = inf {t \| packs n t}` (`shared/squares_defs.ml`) |
| squares | open squares of side 1, with `Inside` contained in [0,L]² | images of the closed square [0,1]² under isometries, contained in [0,t]² |
| disjointness | pairwise disjoint open squares | pairwise disjoint interiors |

The two sets of admissible sides are the same, so the two constants are equal.  This is an
informal argument, not a HOL theorem; the HOL result does not depend on it.
- **Squares.**  A Lean `OpenSquare` with `side = 1` is the open set
  `{(x,y) | loU < c x + s y < loU + 1 /\ loV < -s x + c y < loV + 1}` with `c² + s² = 1`,
  i.e. the interior of a rotated and translated copy of [0,1]².  A HOL `unit_square` is the
  image of the closed [0,1]² under an isometry.  An isometry of the plane is a rotation or a
  reflection followed by a translation, and a reflected copy of [0,1]² is also a rotated and
  translated copy.  So the HOL unit squares are exactly the closures of the Lean unit
  squares, and the Lean squares are exactly their interiors.
- **Containment.**  Lean asks for the open square to lie in the closed box [0,L]²; since the
  box is closed, this holds iff the closed square lies in it, as HOL asks.
- **Disjointness.**  Lean asks for the open squares to be disjoint; HOL asks for the
  interiors to be disjoint.  By the above these are the same sets.
- **`0 < L`.**  Lean's extra condition is implied: a unit square fits only in a container of
  side at least 1.  (`PACKS_12` shows that both sets are exactly [4, ∞).)

The HOL definitions were written independently of Lean, using HOL Light's standard notions, and
nothing is transported from the Lean definition.  The HOL chain starts from `packs` directly:
`PACKS12_NORMALIZE` is Lean's `UnitPacking.normalize`, and `NPACK` matches Lean's
`NormalizedPacking` field by field (`audit.md` §1).

## 2. Correspondence of the developments

| Lean | HOL Light | notes |
|---|---|---|
| `source/S12` (Phase 1: normalization, markers, groups, families, hulls, budgets, symmetry, cores, local queries) | `n12/phase1/` | Lean uses `native_decide` for the finite checks; HOL uses kernel computation (`families_check.ml`, `step6.ml`) |
| `source/S12` pose semantics (angles, poses, coverage, overlap certificates) | `n12/certlib/` | one HOL file per Lean module (`certlib/README.md`) |
| `Compact/Geometry`, `Compact/Bridge`, `Compact/Preservation`, `Compact/Completion` | `n12/geometry/` | one HOL file per Lean module (`CP_` prefix for `Compact/Completion/...`); theorems carry `(* Lean: name *)` |
| `Compact/Cases`, `Compact/Historical*`, `Compact/Core` (data-driven certificates) | `n12/cert/` | reflective checkers proved sound once, then evaluated on the extracted data (`cert_design.md`) |
| `Compact/Assembly` (117-case table) | `n12/cases/`, `n12/assembly.ml` | template cases through a generic bridge; the rest through per-case closers |

Every module in the import closure of `Compact.Assembly.Final` that is not a certificate or
template module has a HOL counterpart (`audit.md` §5).  The certificate and template modules
are re-implemented in `n12/cert/`, `n12/certlib/` and `n12/cases/`.

## 3. Differences in the statements

None of these weakens a conclusion or adds a hypothesis that the packing context does not
supply.

- **Squares** are 5-tuples `c s u v a` (unit normal, offsets in the rotated frame, side) instead
  of Lean's `OpenSquare` structures.  Lean's structure invariants (`c² + s² = 1`, `0 < a`)
  become explicit hypotheses, and squares obtained from existentials carry them explicitly.
- **Finite checks.**  Lean's `decide`, `native_decide` and custom `Check` commands become
  either kernel computation, or OCaml producers that check the data and then build the HOL
  theorem with the kernel.  The OCaml check only decides whether a proof is attempted
  (`audit.md` §3).
- **List.Perm** is rendered as equal occurrence counts (`Bridge/CoverageReorder`).
- **Universal premises** such as `apart` for all pairs are sometimes replaced by the specific
  instances that are used.  The HOL statement is then at least as strong.
- **Proofs** are not ported literally:
  - `nlinarith` becomes `NLIN_TAC` (`shared/tools/nlin.ml`);
  - trigonometric and derivative arguments become half-angle algebra or Bernstein bounds;
  - triangle certificates become the linear arithmetic they certify.

  Statements are unaffected.
- **Not ported:** the trigonometric lemmas of `C983/F4MergedCenterMonotone` and
  `F4BarAngleScalars` (`canonical_angle`, `Bminus`, `Bplus`, `G` and their monotonicity
  lemmas).  The theorems that use them downstream (`positive_comparisons`, `vertex_gap`) are
  ported with trigonometry-free proofs (`audit.md` §2).

## 4. What the port showed about the Lean sources

The Lean development had not been independently built or reviewed (squaremath.org T-245).  Its
README says that the accepted CI run "reused every project object from cache; it was not a fresh
rebuild".  It also says that verification inherits trust in 1,624 approved native-generated axioms
(from `native_decide`).

- **Uncompiled files.**  Many Lean files carry header comments such as "Source only,
  uncompiled", "has not been compiled" or "no compiler replay"; a text search finds about 285
  under `Compact/`, most of them in `Completion/C1092` and `Completion/OtherCases`.  The Lean
  README calls these comments historical.  Every such file on the path to the final theorem was
  ported, and all of its theorems were proved in HOL **as stated**.  No statement needed a
  correction.
- **Native computation.**  All finite checks that Lean delegates to `native_decide` (in
  `source/S12`) are re-done in HOL by kernel computation.  The final HOL theorem uses only
  HOL Light's three standard axioms.
- **Conditional results.**  Several Lean files are explicitly reductions or conditional
  results, not case closers.  Examples:
  - `C981.lean` proves `Obligations -> ExcludesCase 981`;
  - `C1092/MMMP/ProfileAdapter.branch_of_profile` assumes a `StrongNortheast` derivation;
  - `C1090/ResidualEnding` and `C1089/LastSectorEnding` take their entrance inputs as
    hypotheses.

  These were ported as conditionals.  In every case another file of the development closes the
  case outright, and the HOL proof uses those closers.  All 117 rows are closed without
  hypotheses.
- **Minor observations** (no effect on correctness):
  - `positive_transverse_coefficient` in `C1092/MPPMInwardSmallThreeBoundaryScalars.lean` has a
    hypothesis `kn : 0 ≤ k` that its proof never uses.  HOL keeps it, to stay faithful.
  - In `Cases/FourSquareConvex/Case864` and `Case1002`, the triangle certificate for owner 3
    at (3, 12/5) is redundant: the point is already among the query points.
  - In `MergedPending/CentralPoints.lean`, `upper_merged_inward` and the `southeast_*` lemmas
    are vacuous for family `c700`.
  - `C983/F4BottomMidpointOriginal.lean` keeps a corner seed as an explicit hypothesis (its
    docstring explains that the intended route imports a module that is absent).  The HOL
    theorem keeps the same hypothesis.

In short, the HOL port confirms the Lean development: every statement it relies on holds as
written, with all finite computation re-checked by the HOL kernel and nothing taken from Lean's
build cache.

# Design map: the data-driven certificate machinery in Jatloe's N12 Lean proof

Lean repository: Queuingtheorydotcom/Jatloe12SquaresFormalized, commit d0caf45 (a clone is expected in
`n12/ext/jatloe/`).  Lean root: `Lean/Proofs/N12-jatloe/`; all Lean paths below are relative to it.
This document describes the Lean development as found before the port; `lean_comparison.md`
summarizes how the HOL port corresponds to it.  Three lake libraries are involved:

- `Compact/` (`lean_lib Compact`)
- `source/S12` (`lean_lib S12`)
- top-level `Completion/` (`lean_lib Completion`). This is **not** the same directory as
  `Compact/Completion`.

The import closure of `Compact.Assembly.Final` has 5,377 modules.

Not in the closure, so not needed:

- `Core/{Dag, DirectLinear, LinearCombination, IntegerSupportCase}` (the Core README describes
  these, but nothing imports them);
- `Bridge/{BorderEndpoint, C977DisjointChain}`.

There is no `native_decide` anywhere in `Compact/`. Every finite check is a `decide +kernel`, and
every custom command or `%`-elaborator only *emits data*. The kernel re-checks that data against
the dictionaries. Data inherits native-compiler trust only from `source/S12` (Phase 1, already
done in HOL).

---------------------------------------------------------------------------------------------------

## 0. Executive summary

1. **Final theorem.** `N12Compact.Final.optimality : S12.packingConstant12 = 4`
   (`Compact/Assembly/Final.lean`).
   - It is `SourceAssembly.optimality SourceAssembly.pending_closed`.
   - That is `Remaining117.optimality registry _`, which uses `packing_reduction_to_117` (the
     Phase-1 reduction, already proved in HOL as `S12_REDUCED_117`) and one `ExcludesCase id` per
     retained id.
   - The registry is `SymbolicRegistry.registry` (79) ++ `historicalRegistry` (7) ++
     `NewCases.registry` (31) = 117.
2. **Only 7 cases use large certificate data:** 701, 713, 717, 973, 978, 979 ("historical"
   pose-pruning) and 898 (the same idea with its own dictionary and slightly different plan
   types).
   - These account for HistoricalCommon (4.5 MB), HistoricalData (6.7 MB), HistoricalFans,
     Preservation (1.1 MB) and `Cases/C7xx,C9xx,C898` (~7.8 MB).
   - Every other case is template geometry plus small finite ownership enumeration, or a
     hand-written continuous proof.
3. **The certificate mathematics is planar linear arithmetic.**
   - A *pose* is (angle interval, finite list of integer half-planes in the centre
     `(cx, cy)` of one square).
   - Every checker proves one of the following:
     - (a) a 2-variable linear implication (integer Farkas with ≤ 2 rows + slack, strictness
       tracked);
     - (b) a 4-variable implication "two polygons ⇒ 8 separating-axis gaps are positive", built
       from two 2-variable vertex-support bounds;
     - (c) "a fixed rational point is in the inner reference square for every centre in the
       polygon" (4 support bounds);
     - (d) "target rows are ≥ 0 on a bounded region minus open convex blocks" by checking all
       pairwise line intersections (vertex enumeration).
   - Plus a few fixed geometric lemmas:
     - SAT for two squares;
     - inner/outer reference squares of an angle enclosure;
     - four long sections cannot share one line (already ported in `n12/geometry/SectionCapacity.ml`
       and `LongSection.ml`);
     - Phase-1 local queries and ownership domains (already in HOL: `localq.ml`, `step6.ml`).
4. **Volume.** Historical cases total:
   - ~9.2k pruning plans with ~90k target-row hints;
   - ~1.9k overlap groups covering ~640k (source, neighbour) pairs, of which ~227k are explicit
     8-axis pair checks and ~53k are common-point context checks;
   - 13.3k fan contexts over a 114,465-row / 28,235-pose dictionary;
   - ~6.1k initial vertex-enumeration recipes;
   - 1.3k chord plans and 3.0k chord neighbours.

   C898 adds:
   - 601 plans, 927 relaxation links;
   - ~25.8k pair-overlap claims, 1,063 fan contexts;
   - 704 initial recipes, 54 chord plans and 312 chord neighbours.

   All of it is integer arithmetic on numbers ≤ ~10^16 (products ~10^35). This is feasible for a
   HOL checker *proved once and evaluated* (see §8), but not as one HOL proof term per inequality
   built naively by `REAL_ARITH`.

---------------------------------------------------------------------------------------------------

## 1. Compact/Assembly: final theorem and the 117-case table

### 1.1 Chain

- `Final.optimality` comes from `SourceAssembly.optimality (work : Pending)`
  (`Assembly/SourceAssembly.lean`), which comes from `Remaining117.optimality registry
  (pending_exclusions work)` (`Assembly/Remaining117.lean`).
- `Remaining117.optimality` applies `packingConstant12_eq_four_of_exclusion`, then
  `packing_reduction_to_117 p : ∃ t r, r ∈ retainedRows ∧ codedMarkerFamily (t.pullPacking p) =
  r.groups`, then `retained_exclusions`.
- `ExcludesCase id` (in `Completion/Contracts.lean`) is
  `∀ r ∈ retainedRows, r.originalId = id → ∀ p : NormalizedPacking, codedMarkerFamily p =
  r.groups → False`.
- Every whole-case proof starts with `RowIdentity.family_at k id family (by decide +kernel)`
  (`Assembly/RowIdentity.lean`). This binds the case's literal family Finset to row `k` of
  `coverRows`, reusing the Phase-1 `survivors_distinct`.
- `SourceAssembly.pending_ids_exact : pendingIds = ∅`. The `Pending` structures in
  `SourceAssembly` and `ContinuousRemaining` are historical. They are discharged by default
  fields `C981Compact.pending_closed` and `C1092Compact.pending_closed`.
- `SymbolicRegistry.lean`, `NewCases.lean`, `SourceAssembly.historicalRegistry` and
  `C981Progress.lean` are only lists of `⟨id, proof⟩`. `C981Progress` regroups 42 C981
  representative ids. It is informational and is subsumed by `Cases/C981Registry`.

### 1.2 Case table (117 ids)

"Template" means the four-square template geometry (already handled). "Finite+hand" means a small
decidable ownership enumeration plus hand geometry. "Cert" means large certificate data with a
kernel-checked checker.

| ids | Assembly entry | proving module(s) | mechanism |
|---|---|---|---|
| 28,78,537,556,565,567,569,570,575,576,577,585,1085,1086,1087 (15) | `FourSquareCases.covered_cases_excluded` | `Cases/FourSquare*` | template (done) |
| 405,424,985,990,993,994,999,1063,1064,1069,1070 (11) | `FourSquareVariantCases` | `Cases/FourSquareVariant` | template (done) |
| 445,454,862,864,992,995,998,1001,1002 (9) | `FourSquareConvexCases` | `Cases/FourSquareConvex` | template (done) |
| 678,680,691,694,711,846,847,852,853,886,887,1073,1074 (13) | `FourSquareHighRightCases` | `Cases/FourSquareHighRight` | template (done) |
| 841,842 | `FourSquareUnusedCases` | `Cases/FourSquareUnused` | template (done) |
| 669,670,673,674,675,690,848,850 (8) | `FourSquareHighRightExtraCases` | `Cases/FourSquareHighRightExtra` | template (done) |
| 71,80,589,590 | `MergedLowerCases.covered_cases_excluded` | `Cases/MergedLower/{Helpers,Domains7180,Domains589590,Recipes,Complete}` | finite domain enumeration → 12 recipes (`FourSquareCase` / `MidpointCase`) via `Bridge/FourSquareVectorCover` |
| 684 | `Endpoint684Assembly.excludes_case` | `Cases/Endpoint684.lean` | 9 domains, 6 patterns → `FourSquareCaseHighRight` / `Bridge/EndpointHighRightCase` |
| 849,851 | `C849851Assembly.excludes849/851` | `Cases/C849851/{Ownership,Positive,Complete}` | forced owners (`feasible … = false`) + hand geometry (`Geometry/C849*`, ported) |
| 697,698,699 | `MergedTopFurtherAssembly` | `Cases/MergedTopFurther/{Ownership,Geometry,Complete}` | forced owners + hand geometry |
| 709,882,890,1075,1077,1078,1081,1083 | `OppositeCentralWallsAssembly` | `Cases/OppositeCentralWalls/{Ownership,Complete}` | 6 forced owners + `Geometry/CentralWallCenter` under 2 transforms |
| 696 | `C696OwnedWestClosure.excludes` | `Bridge/C696*` (11 files) + `Completion/Cases/C696/*` | hand proof (+ Phase-1 `SingleSpec` data) |
| 84 | `C84Assembly.excludes_case` | `Bridge/C84{Complete,Ownership,MergedBottomDomain}` | finite ownership + `Geometry/C84MergedPair` (ported) |
| 977 | `C977CenterClosure.excludes` | `Bridge/C977*` (37 files) + `Completion/Cases/C977/*` | hand proof (`Bridge/CongruentSAT` is a theorem, not data) |
| **701** | `Preservation.Complete.C701.excludes_case` | `Cases/C701`, `HistoricalCommon/C701`, `Preservation/{C701,Chords/C701Step*}` | **cert: historical pose pruning** |
| **713** | `Preservation.Complete.C713.excludes_case` | `Cases/C713` (incl. `HeightData`, `ChordDirect`), `HistoricalCommon/C713` | **cert** |
| **717** | `Preservation.Complete.C717.excludes_case` | `Cases/C717`, `HistoricalCommon/C717`, `Preservation/{C717,Chords/C717Step17,18}` | **cert** |
| **898** | `C898.excludes_case` | `Cases/C898/*` (own dictionary) | **cert** (§4) |
| **973** | `Preservation.Complete.C973.excludes_case` | `Cases/C973`, `HistoricalCommon/C973`, `Preservation/{C973,Chords/C973Step*}` | **cert** |
| **978** | `Preservation.Complete.C978.excludes_case` | `Cases/C978`, `HistoricalCommon/C978`, `Preservation/{C978,Chords/C978Step11,13}` | **cert** |
| **979** | `Preservation.Complete.C979.excludes_case` | `Cases/C979`, `HistoricalCommon/C979`, `Preservation/{C979,Chords/C979Step*}` | **cert** |
| 48,573,574 | `NewCases` | `Compact/Completion/CommonCases/C48Rows` | completion (hand) |
| 580,581 | `NewCases` | `Compact/Completion/FiniteCases/C580581Completion` | completion |
| 683,700,867 | `NewCases` | `Compact/Completion/OtherCases/MergedPending/{Completion,C700Completion}` | completion |
| 702, 888, 889, 893, 982, 1072, 1084 | `NewCases` | `Compact/Completion/CommonCases/*` | completion |
| 705,716 | `NewCases` | `Compact/Completion/OtherCases/C705716` | completion (uses `HistoricalOwnership` local queries and `split_kernel_check`) |
| 715 | `NewCases` | `Compact/Completion/OtherCases/C715` | completion (uses `certified_query%`) |
| 868 | `NewCases` | `Compact/Cases/C868/*` (27 files, 158 KB) | finite ownership + hand geometry (no cert data) |
| 896, 972, 975, 997 | `NewCases` | `Compact/Completion/FiniteCases/*` | completion |
| 974, 976, 1089, 1090, 1091 | `NewCases` | `Compact/Completion/OtherCases/*` | completion |
| 983 | `NewCases` | `Compact/Completion/OtherCases/C983` | completion (uses `HistoricalOwnership` queries, `checked_local_query`) |
| 981 | `NewCases` | `Cases/C981Compact.lean` → `Cases/C981{,Registry,V116}.lean` + `Completion/Cases/C981/*` + `Compact/Completion/C981` + `Bridge/C981*` | finite vector coverage (~10k prefix rows) + 117 hand representative proofs (§5) |
| 1092 | `NewCases` | `Cases/C1092Compact.lean` → `Bridge/C1092*` + `Compact/Completion/C1092` (364 files) | D4 classification into 4 branches + hand endings (§5) |

Counts: 58 template + 4 + 1 + 2 + 3 + 8 + 3 = 79 symbolic, plus 7 historical, plus 31 new = 117.

The only Completion modules that consume historical data objects are:

- `OtherCases/C983` and `OtherCases/C705716`, which use `HistoricalOwnership.Queries`;
- C1092, which uses `Cases/C979/EntryQueryChunks/Chunk11,17` through `Bridge/C1092AuxiliaryCover`.

So `HistoricalOwnership` (a list of Phase-1-type local queries) is needed even outside the
historical cases.

---------------------------------------------------------------------------------------------------

## 2. Shared semantic layer (source/S12 and the Dictionary)

### 2.1 Squares, angles and poses

- `S12Pilot.OpenSquare` is `⟨c, s, loU, loV, side⟩`. `Inside x y` is
  `loU < c x + s y < loU+side ∧ loV < −s x + c y < loV+side`. In HOL this is `linside c s u v a`
  (`n12/geometry/p2_base.ml`).
- `NormalizedPacking` (Phase 1) has 12 squares, a common side `a ∈ (1, 1001/1000]`, all inside
  `[0,4]²` and pairwise disjoint. `ownerIndex p mask` is the square owning that marker group.
- **`S12.AngleEnclosure`** (`source/S12/AngleEnclosure.lean`) is `⟨lower, upper, c, s, outer,
  inner, wall⟩ : ℚ⁷`.
  - The parameter is the rational half-angle t ∈ [lower, upper] ⊆ [0,1] with
    `normalC t, normalS t` (rational parametrisation of the first-quadrant unit circle).
  - `Check` requires:
    - `c²+s²=1`, `0 < outer`, `0 < inner`, `inner·outer ≤ 1`;
    - four `supportQuadratic … .CheckOn lower upper` (quadratic nonnegativity on the interval,
      `S12.QuadraticInterval`);
    - `wallQuadratic wall .CheckOn`.
  - Consequences:
    - `outer_sound` (`PoseBounds`): every square with that angle and side ≤ 1001/1000 lies in the
      outer reference square `(c, s, 1.001·outer)` around its centre.
    - `inner_sound` (`AngleReference`): it contains `w.reference 1 = (c, s, inner)` around its
      centre.
    - `wall_sound`: its centre is in `[wall/2, 4 − wall/2]²`.
  - The data are in `S12.AngleData64` (64 enclosures) and `S12.AngleData128` (128).
  - `C713Shared.angles : Fin 192 → …` concatenates them. Index < 64 is the 64-grid; index ≥ 64 is
    the 128-grid.
- `S12.CoversInterval l h ws` (`IntervalCoverage.lean`) is a chained interval cover of
  `[l, h]`, decided.
- **`S12.PoseLeaf`** is `⟨angle : {w // w.Check}, inputs : List (LinearConstraint 2)⟩`
  (`OwnerEnclosure.lean`). For a square q:
  - `PoseLeaf.Realizes q` means all inputs hold at `(centerX q, centerY q)` **and** the inner
    reference square translated to q's centre is ⊆ q.
  - `OrientedRealizes q` adds `AngleWitness`: q, with some face indexing, has half-angle t in
    `[lower, upper]` (`OrientedCoverage.lean`).
  - `OrientedPoseCovered L q := ∃ leaf ∈ L, leaf.OrientedRealizes q`. Every stage theorem is
    stated with this predicate.
- `S12.poseInputs w inside` (`PoseRegion.lean`) is a list of rows:
  - for every inside point P, the 4 rows saying P is in the *outer* reference square at the
    centre;
  - the 4 wall rows;
  - the row `1 > 0`.
- `S12.poseForbidden w outside` gives, for every outside point P, the 4-row block "P is in the
  *inner* reference square". Such a block cannot hold entirely.

### 2.2 Integer rows and the dictionary

- **`IntegerSupport.Row`** (`Compact/Core/IntegerSupport.lean`) is `⟨x y constant : ℤ, strict :
  Bool⟩`.
  - `Holds p := if strict then 0 < x·p₀ + y·p₁ + c else 0 ≤ …`.
  - `Row.normalized den` is the S12 `LinearConstraint 2` with coefficients divided by `den`, and
    `normalized_holds_iff` holds for `den > 0`. Denominators therefore matter only for
    faithfulness to the S12 pose data. **For checking, only the integer row matters.**
- **`IndexedRelaxation.Dictionary n m a`** (`Bridge/IndexedRelaxation.lean`) is
  `⟨rows : Fin n → Row, denominators, angles : Fin a → {w // w.Check}, poseAngle : Fin m → Fin a,
  poseRows : Fin m → List (Fin n)⟩`.
  - `Dictionary.pose i : PoseLeaf := ⟨angles (poseAngle i), (poseRows i).map normalized⟩`.
  - **`Dictionary.transfer`**: if `poseAngle s = poseAngle t` and every row of `t` holds at q's
    centre, then `(pose s).OrientedRealizes q → (pose t).OrientedRealizes q`. The angle data are
    identical, so the inner-reference and angle witnesses carry over. This is the *only*
    pose-level semantic step. All numerical checking reduces to "the target rows hold at the
    centre".
  - `Link`, `Support`, `cover_sound`: the same as transfer, with target rows derived by
    `RowSupport` from 2 source rows.
- **Historical dictionary.** `C713Shared.dictionary` (`Cases/C713/SharedDictionary.lean`) is shared
  by all six historical cases.
  - `HistoricalData.rowCount = 114465`, `poseCount = 28235` (`HistoricalData/Counts.lean`).
  - `Preservation/HistoricalDictionary.lean` re-exports it as `HistoricalBank.dictionary`.
  - C898 has its own dictionary (§4).

---------------------------------------------------------------------------------------------------

## 3. Historical pose-pruning pipeline (C701, C713, C717, C973, C978, C979)

### 3.1 Case-level shape

The proof follows the same plan for every one of these cases. Take C713 as the example
(`Cases/C713/Assembly.lean`, `Cases/C713/DirectPruning/All.lean`,
`Preservation/Complete/C713.lean`):

1. **Entry.** For each owner k (one of the 12 masks of the family) there is
   `CK_Entry.ownerK_cover p hf : OrientedPoseCovered domainK_0 (p.square (ownerIndex p maskK))`,
   with `domainK_0` a list of pose ids (§3.2).
2. **Pair stages.** A fixed sequence of stages, each of type
   ```
   PairTransition S N T := ∀ q t, OrientedPoseCovered S q → OrientedPoseCovered N t →
       (∀ x y, ¬(q.Inside x y ∧ t.Inside x y)) → OrientedPoseCovered T q
   ```
   Here q is owner A's square and t is owner B's square (A ≠ B, so the two squares are disjoint).
   The stage shrinks A's pose list using B's current pose list. This is §3.3 plus §3.4.
3. **Special stages.** Some stages use four squares (chord) or an occupied-row height bound
   (§3.5).
4. **End.** The final stage produces an empty pose list for some owner. The proof closes with
   `obtain ⟨leaf, member, _⟩ := after_last; exact List.not_mem_nil member`.

The chains are fixed per case. Owner masks and domain-id lists are in
`Cases/CK/SharedDomains.lean` (C713) or `Preservation/CK.lean` (the others, which also hold the
`Pending` record of the chain). The final theorems are
`CK_DirectPruning.excludes_case_of_remaining overlaps remaining` and
`C713DirectPruning.family_impossible_of_block_overlaps`.

The remaining fields come from three places:

- `Remaining.initialK` from `CK_Entry.ownerK_cover`;
- `Remaining.stepN` for chord stages from `Preservation.Chords.CK_StepNN.packing_sound`;
- `BlockOverlaps.stepN` from `HistoricalCommon.CK.StepNN.block_overlaps`.

| case | pair stages (DirectPruning) | chord stages (Preservation/Chords) | other | owners with initial cover |
|---|---|---|---|---|
| C701 | 26 (Step00–05, 07–13, 15–19, 21, 22, 24–27, 29, 30) | 6, 14, 20, 23, 28 | — | 12 |
| C713 | 9 (0–4, 6–9) | — | step 5 = occupied-row height (`C713ChordDirect`, `HeightData`, 108 records) | 9 |
| C717 | 17 (0–16) | 17, 18 | — | 11 |
| C973 | 23 | 10, 11, 15, 25, 26 | — | 11 |
| C978 | 14 | 11, 13 | — | 9 |
| C979 | 24 | 17, 20, 21, 24, 27, 28 | — | 12 |

### 3.2 Entry: initial owner covers (RecipeInitial, Entry*)

**Statement.** `DirectPoseCover.CertifiedOwner.sound` (`Bridge/DirectOwnerFamily.lean`) gives
`OrientedPoseCovered owner.target (p.square (ownerIndex p owner.domain.mask))`.

**Ingredients.**

- **Ownership domain** `CertifiedDomain family` (source/S12, Phase 1). It is built in
  `Cases/CK/EntryDomains.lean` with `.ofDirectProduct single_k_0 single_k_1 …`, `.remove … query
  …` and `.refineAgainst`. The `DirectSingleDomain`s and `LocalQuery`s used are in
  `EntryQueries*.lean`, `EntryQueryChunks/*`, `SharedSelections/*` (C979) and
  `HistoricalOwnership/Queries*.lean`.
  - The queries are S12 `LocalQuery` records of kinds `.hull` / `.four` / short, the same type as
    the 1,703 Phase-1 queries. HOL `localq.ml` already checks this type.
  - New ones are declared with `checked_local_query X := ⟨mask, kind, owned, cert⟩` and existing
    ones selected with `certified_query% n` (`Bridge/SharedLocalQueries.lean`).
- **Points.** `CertifiedPoint` common points (`EntryPoints.lean`, `.ofDomainHull … OwnedHullPoint`)
  and `PointPremises.Check domain known inside outside` (`Bridge/PointPremises.lean`).
  `PointPremises.sound` turns these into real `q.Inside P` for P ∈ `insideK` and `¬q.Inside P`
  for P ∈ `outsideK` (`Cases/CK/RecipeInitial/Inputs.lean`).
- **Enclosure** `DirectPoseCover.Owner = ⟨inside, outside, roots⟩` (`Bridge/DirectPoseCover.lean`).
  - `Owner.Check` requires `CoversInterval 0 1` of the root angles. All 64 or all 128 angles are
    present, e.g. `C713Shared.angles128_cover_kernel`.
  - Each `Root = ⟨angle, base, forbidden, result : Option (List Form)⟩` passes **`Root.Check`**:
    - `BoxNormals base` (rows with normals +x, −x, +y, −y exist, so the region is bounded);
    - `PlanarVertexCheck.Check baseRows forbiddenRows targetRows`;
    - base forms ∈ `poseInputs angle inside`;
    - forbidden blocks ∈ `poseForbidden angle outside`;
    - `strictOK` (target rows non-strict, or constant positive).
  - `targetRows` is the target pose's rows, or `[⟨0,0,−1,false⟩]` when `result = none` (an empty
    angle cell).
  - **`Root.sound`**: every square with that angle that contains `inside` and avoids `outside`
    realizes the result pose.
- **Data format.** `Cases/CK/RecipeInitial/Batches/OwnerKKBatchJJ.lean` uses
  ```
  checked_initial_batch NS (bank, insideK, outsideK)
    [ entryK_i := ⟨angleIdx, [input row positions in poseInputs], some poseId | none⟩, … ]
  ```
  with ≤ 8 records per batch.
  - `checked_initial_batch` is defined in `Bridge/InitialCoverBatch.lean`. It expands each record
    through `checked_recipe` (`Bridge/CheckedRecipeCommand.lean`).
  - The record type is `DirectRecipeTable.Spec` (`Bridge/DirectRecipeTable.lean`), with checker
    `DirectRecipeTable.Entry.Check`, which is BoxNormals ∧
    `PlanarVertexSparse.triangle (PlanarVertexCheck.PairCheck …) activeRows` ∧ strictOK.
  - `active` lines come from `PlanarBoundaryHints.Cache` (`Core/PlanarBoundary{Filter,Hints,Auto}`,
    `Core/BoundaryHintSyntax`). These remove lines on which no base-feasible point exists, each
    certified by a parallel-row `LineExclusion`.
  - `Bank` is `DirectRecipeTable.Bank.ofDictionary dictionary` (`Bridge/DirectRecipeDictionary`,
    `Preservation/InitialBank.lean`). `ownerK_leaves_shared` proves that the produced leaf list is
    the literal `domainK_0`.
- **Core math** (`Core/PlanarVertex.lean`: `nonnegative_of_vertices`;
  `Core/PlanarVertexCheck.lean`: `Check.sound`). Let

  F = {p : base rows ≥ 0 (closed) ∧ ∀ block, ¬(all block rows > 0)},

  where `base` contains the four box normals. If every target row is ≥ 0 at every point of F
  that is the intersection of two non-parallel lines from `base ∪ ⋃blocks`, then every target
  row is ≥ 0 on all of F.
  - `PairCheck a b`: `det a b = 0`, or (`vertex a b` feasible → every target ≥ 0 at it).
  - The vertex is computed exactly as an integer triple `(x, y, den)` (`PlanarVertexCheck.vertex`).
  - Strict input rows are deliberately weakened to closed rows. Strictness of outputs is handled
    by `strictOK`.

### 3.3 Pair stages: `checked_blocked_batch` plans (Cases/CK/DirectPruning)

**Data** (`Cases/CK/DirectPruning/StepNNBatchMM.lean`):
```
checked_blocked_batch NS (C713Shared.dictionary) [
  plan8 (1947,(some [109454]),2075) [.direct (.single 0), .block [.pair 0 2], …, .direct (.copy 12)],
  planX empty(1960), … ]
```

Each record is `(source pose id, block : Option (List rowId), target pose id)` with one hint per
target-pose row, in order.

- **Command.** `checked_blocked_batch`, with record syntax `blockedTargetRecord` and term macro
  `cached_blocked_target%(dict, src, block, tgt)[hints]`, in
  `Bridge/IndexedBlockedTargetSyntax.lean`.
  - It materializes `inputs = poseRows src`, `blocked = block rows` and
    `outputs = poseRows tgt` as `Row` literals with `materialize_rows%`
    (`Core/RowMaterializeSyntax.lean`).
  - It emits `def planN` and `theorem planN_checked : Plan.Check planN dict := by decide +kernel`.
- **Type.** `IndexedBlockedTarget.Plan r m = ⟨source, block, target : Option, inputs, blocked,
  outputs, hints : List (BlockedTarget.Hint inputs.length)⟩` (`Bridge/IndexedBlockedTarget.lean`).
- **Checker `Plan.Check plan d`:**
  - `target = none` → `block = some []`. The source pose is wholly excluded by the overlap
    argument.
  - `target = some T` → the row lists match the dictionary, `poseAngle src = poseAngle T`, and
    `BlockedTarget.Check inputs blocked outputs hints` holds. If `block = none`, all hints must be
    "independent" (not `.block`).
- **`BlockedTarget.Hint`** (`Core/BlockedTarget.lean`) handles one target row τ:
  - `.direct h` — `RelaxationHints.Hint.Check inputs τ`, i.e. the source rows imply τ;
  - `.block hs` — from `opposite τ :: inputs` (index 0 = ¬τ), every block row is derived
    (`RelaxationHints.Check (opposite τ :: inputs) block hs`). So S ∧ ¬τ ⇒ B;
  - `.impossible w` — `EmptyContext.Witness` on `opposite τ :: inputs` (S ∧ ¬τ is infeasible).
    This occurs 0 times in the historical data.
- **`RelaxationHints.Hint`** (`Core/RelaxationHints.lean`) is one of:
  - `.constant` (τ is `c ≥ 0` with c ≥ 0);
  - `.copy i` (τ equals source i);
  - `.single i` (τ is a positive multiple of source i plus nonnegative slack, using
    `RowSupport.one = (0,0,1,strict)`);
  - `.pair i j` (`RowSupport.Check a b τ`: Cramer weights `PairSupport.cramer a b τ.x τ.y`,
    slack on `1 > 0`, checked by `SparseInteger.Certificate.Check`).
- **Plan soundness `Plan.sound`.** Let `S` be the source pose region, `B` the block conjunction
  and `T` the target pose. Then `(pose S).OrientedRealizes q ∧ ¬(B holds at centre q) ⇒
  (pose T).OrientedRealizes q`. Mathematically: for each τ ∈ T, either S ⊆ {τ} or S ∩ {¬τ} ⊆ B;
  hence S \ B ⊆ T.
- **Stage.** `Stage.Check` requires:
  - `plans.map source = sources` (literally the list of source pose ids, in order);
  - `TargetsIn plans targets`;
  - all plans checked.

  This is assembled in `Cases/CK/DirectPruning/StepNN.lean` (`stage`, `stage_checked`,
  `step_sound`).
- **`Stage.BlockOverlap`** is the remaining geometric premise:

  ∀ header (src, some B) ∈ plans, ∀ q t, (pose src).OrientedRealizes q →
  OrientedPoseCovered (neighbors.map pose) t → B holds at centre q → ∃ x y, q.Inside x y ∧
  t.Inside x y.

  **`Stage.step_sound`** is the `PairTransition`. It is discharged by HistoricalCommon (§3.4).
- In the data, block rows are almost always 1–4 dictionary rows (`fanBlockRows k`, below). The
  hint indices refer to positions in the materialized lists, not to dictionary ids.

### 3.4 Block overlaps: HistoricalCommon (+ HistoricalData, HistoricalFans)

**Statement.** `HistoricalCommon.CK.StepNN.block_overlaps : CK_DirectPruning.StepNN.BlockOverlap`
(`HistoricalCommon/CK/StepNN.lean`). It comes from
`IndexedCommonGroups.block_overlap_headers` (`Bridge/CommonHeaderPruning.lean`), using:

- `sourceHeaders_exact`, `planHeaders_exact` and `source_matches`: each plan header
  `(src, some B)` equals the header of one source context;
- `neighbors_exact`: the neighbour contexts are exactly the neighbour domain, all unblocked;
- `pairs i j : PairOverlaps (sources i) (neighbors j)` for all i < u, j < v.

`PairOverlaps x y := ∀ q t, x.header.Realizes q → y.header.Realizes t → ∃ point in both`, where
`Header.Realizes` = `(pose).Realizes q` ∧ block rows hold at the centre.

**Rectangle covering.**

- `partition : RectanglePartition` (`Bridge/CommonRectanglePartition.lean`) is a binary tree of
  `.sourceCut k` / `.neighborCut k` / `.leaf`.
- `partition.Check ⟨0,u,0,v⟩ scopes` (decided) says that every leaf rectangle is one of the group
  scopes. `RectanglePartition.sound` gives `ScopeCheck`.
- `groups_sound` (`Bridge/IndexedCommonGroups.lean`) combines this with one `CheckedGroup` per
  scope.

**Group commands** (`Bridge/CheckedCommonGroup.lean`), in
`HistoricalCommon/CK/StepNNGroupsMM.lean`:

- **`checked_point_group g (sources, neighbors, positive, ownKeys) : u × v in (s, sc, n, nc) at
  ⟨x, y, den⟩`.** One rational point P = (x/den, y/den) serves a whole rectangle.
  - It emits two `kernel_matrix` facts (`Core/KernelMatrix.lean`; chunks of 8, each
    `decide +kernel`): `(sources i).PointCheck ownKeys P` for i in the source range, and the
    same for the neighbour range.
  - Soundness `IndexedCommonGroups.pointGroup` / `IndexedCommonPoint.point_sound` /
    `CommonPoint.inside_sound` (`Core/CommonPoint.lean`): for each of the 4 own face directions
    u_i of the context's inner reference square (side s), every centre c in the context region
    satisfies `u_i · (P − c) < s/2`. Hence P − c ∈ reference square, so P ∈ q. This holds for
    both squares, so they overlap.
  - Check per face (`CommonPoint.axis`): a cached support datum gives `u_i·c ≥ m_i` for c in the
    region (vertex basis with u_i in its cone, below). Then the integer test is
    `2·sideDen·(den_d·(u_i·P_num) + const·P_den) ≤ den_d·P_den·refDen·side`, strict unless the
    datum is strict.
- **`checked_axis_group g (sources, neighbors, positive, pairKeys, opposite) : u × v in (…)`.**
  - It emits `kernel_matrix g_pairs_checked : sc × nc => (sources i).PairCheck (neighbors j)
    pairKeys opposite`.
  - Soundness: `IndexedCommonGroups.fallbackGroup` → `IndexedRawPairPlans.PoseContext.pair_sound`
    → `RawSupportFan.pair_sound` → `ReferenceAxis.overlap` → `S12.axisOverlapForms_sound`.
  - In words: let A and B be the inner reference squares of the two poses (rational c, s, side)
    and R_A, R_B the centre polygons. For each of the 8 directions n ∈ {±u_A, ±u_A^⊥, ±u_B,
    ±u_B^⊥} (`ReferenceAxis.directions`), and all p ∈ R_A, q ∈ R_B:

    n·(p − q) + r_A(n) + r_B(n) > 0, where r_X(n) = side_X/2·(|n·u_X| + |n·u_X^⊥|)
    (`radiusNumerator`, `target`).

    Then A+p and B+q overlap (SAT), and so do the real squares, which contain them.
  - Checker `RawSupportFan.PairCheck a b keys opposite` (`Core/RawSupportFan.lean`): for each
    i : Fin 8, select basis `A = a.select (keys i)` and `B = b.select (opposite (keys i))`. Then
    check:
    - `A.Cone n` (Cramer weights of n w.r.t. A's two rows ≥ 0, so `n·p ≥ n·v_A` on R_A by
      `VertexSupport.Basis.sound`);
    - `B.Cone (−n)`;
    - `VertexSupport.PairCheck A B n.x n.y scale constant`. This is the integer inequality
      `scale·(den_B·(−n·v_A) + den_A·(n·v_B)) ≤ den_A·den_B·constant`, strict or with a strict
      supporting row.
  - The basis selection (binary search on `start` keys) is only a hint. Every selected basis is
    re-checked.

**Contexts.** `HistoricalCommon/Bindings000–414.lean` contain 12,932 records of the form
```
checked_common_fan contextN (dictionary, HistoricalFans.….directions) := ⟨poseId, blockRows⟩
  using [cyclic list of boundary row ids]
```
plus 336 `bind_common_context` (reuse a cache for another header) and 1
`checked_empty_context` (a Farkas witness that the region is empty).

- **Commands.** `checked_common_fan` is in `Bridge/CheckedCommonFanCommand.lean`;
  `bind_common_context` / `cache_common_fan` / `checked_empty_context` are in
  `Bridge/CheckedCommonContext.lean`. The underlying types are `IndexedCommonGroups.{Header,
  Context, FanCache}` and `Bridge/IndexedCommonContext.lean`.
- **What the command does.** It builds `BoundaryFan.context rows (block ++ poseRows) (reference
  angle) directions cycle` (`Core/BoundaryFanSyntax.lean`).
  - Consecutive cycle rows (cyclically) give vertex bases
    `VertexSupport.Basis.fromRowsPrimitive a b` (`Core/VertexFromRows.lean`), with `start`
    computed by binary search of the row normal in `directions`.
  - It materializes the result with `materialize_boundary_fan%` and checks
    `VertexFanTable.RawContext.Check` by `decide +kernel`: rows ∈ inputs, and the vertex lies
    exactly on both rows (`Basis.Check`).
  - It materializes the numeric view with `materialize_raw_fan%`.
  - The reference is `HistoricalPoseFanRecipe.reference angle` (`Bridge/HistoricalPoseFanRecipe`):
    integer `(c·d, s·d, d, inner.num, inner.den)` with `d = lcm(c.den, s.den)`.
- **Keys.** `HistoricalCommon/Keys.lean`:
  - `ownKeys angle i = angleRank[angle] + 192·perm(i)`;
  - `pairKeys` gives source own keys for axes 0–3 and neighbour own keys for axes 4–7;
  - `opposite k = (k + 384) mod 768`.
  - `HistoricalFans/C701_713_717_973_978_979/Directions.lean` has 768 integer directions:
    192 angles × 4 face normals, sorted by polar angle. The key indexes this array, so
    `directions[key]` is the actual axis direction.
- **Fan blocks.** `HistoricalData/SharedFanBlocks.lean`: `fanBlockRows k`, 5,645 small row-id
  lists (`sparse_poses% 1 114465 "k:0;r1,r2,…"`).

**HistoricalData** (6.7 MB) holds the dictionary rows and poses:

- `RowsChunks/Part*.lean` use `strip_sparse_rows% "…"` (`Core/StripRowSyntax.lean`), which
  expands to `boxed_sparse_rows%` (`Core/BoxRowSyntax.lean`) and builds a
  `SparseLiteral.Tree (Row × Nat)` (`Core/SparseLiteral.lean`). Line formats:
  - raw: `id:x,y,c,strict,denPred`;
  - box: `B:left,right,bottom,top;n,d|n,d|n,d|n,d;mask` (4 axis rows `±d·p − n`, bit i =
    strictness);
  - strip: `M:lo,hi;x,y;nlo,nhi;dlo,dhi;mask` or `P:` with two positive scales (a pair of
    parallel rows).
  - Counts: 66,293 raw + 6,298 boxes + 4,007 strips, about 99.5k rows in a 114,465 index space.
- `PosesChunks/Part*.lean` use `sparse_poses% 192 114465 "id:angle;rowIds"`. About 12.7k
  literal pose lines plus inner tree nodes, in a 28,235 index space. A typical pose has 8–13
  rows.
- `SharedRows.lean` and `SharedPoses.lean` assemble balanced trees and define `rows`,
  `denominators`, `poseAngle` and `poseRows` by `SparseLiteral.lookup` with an explicit fallback.
  `positive_denominators` is structural (`denPred + 1`).

**HistoricalFans** (1 file) is just the `directions` array (774 lines).

### 3.5 Chord stages (Preservation/Chords) and the C713 height stage

**Chord.** `Preservation/Chords/CKStepNN.lean`:
```
def horizontal := true/false; lo hi : ℚ
checked_chord_neighbor neighborA_B (dict, horizontal, lo, hi) := (poseId, radiusK, radiusK_checked, [hints])
checked_chord_collection neighborsA : (Neighbor dictionary) => …
checked_chord_plan planN (dict, horizontal, lo, hi) :=
  (srcPose, radiusK, radiusK_checked, chord_close%(⟨rows, terms⟩) | chord_keep%(tgtPose, [hints]), <same for high side>)
```

- The commands are in `Bridge/ChordSyntax.lean`; the types and soundness in
  `Bridge/IndexedChord.lean`.
- `Radius = ⟨sumUpper, radius⟩` with `Radius.Check angle` (`Bridge/AngleSection.lean`):
  `0 ≤ r`, `2r ≤ 1 + B − B²`, and the quadratic `c+s ≤ B` holds on the interval. The
  `radiusK_checked` lemmas are in `Preservation/Chords/Radii.lean` (`norm_num`). Then
  `Radius.bound`: `r ≤ (c + s − 2cs)/2` over the angle interval.
- **Neighbour check.** `Neighbor.Check`: `Radius.Check` ∧ `RelaxationHints` derive
  `centre ≥ hi − r` and `centre ≤ lo + r` from the pose rows. Then `Neighbor.sound`: for every cut
  in [lo, hi], `AxisSection.Section` holds, i.e. the square contains a segment of length > 1 on
  the line `y = cut` (or `x = cut`) (`oriented_section`, using `horizontal_long_section`).
- **Plan check.** `Plan.Check`: `Radius.Check` ∧ two `DirectPruningPlan.Branch.Check`s.
  - Branch `low` has inputs `centre < lo − r` (strict) plus pose rows; branch `high` has
    `centre > hi + r` plus pose rows.
  - Each branch is `.keep target hints` (same angle; RelaxationHints derive all target rows) or
    `.close witness` (`EmptyContext.Witness` Farkas contradiction).
- **Soundness.** `IndexedChord.plans_cover` / `Plan.sound` use `AxisSection.window_excludes`: four
  disjoint squares inside the container cannot all have long sections on one line
  (`four_on_one_cut`, ported in `n12/geometry/SectionCapacity.ml`). So the source square's centre
  is outside `[lo − r, hi + r]`, and one of the two branches applies.
- `ChordPacking.transfer` (`Bridge/ChordPacking.lean`) binds this to 4 distinct owners of the
  packing.
- **Volume:** 20 chord files, 1,298 plans (172 with two `close` branches), 2,963 neighbour
  records, 80 collections.

**C713 height** (`Cases/C713/{ChordDirect,HeightCore,OccupiedRow}.lean`, `HeightData/Batch*`):

- 108 `Entry = ⟨VertexCutRelaxation.Spec ⟨src, cut row, target?⟩, Radius⟩`.
- `OccupiedRow.above_radius` gives centreY(owner 7) > 87/50 + r from the occupied row points.
- The record checks that cut = `y ≥ 87/50 + r`, and runs
  `PlanarVertexSparse.UnorderedCheck base [] targets` (vertex enumeration) to obtain the target
  pose or a contradiction (`Bridge/VertexCutRelaxation.lean`).

### 3.6 HistoricalOwnership and Preservation

- **`HistoricalOwnership/Queries000–068.lean`.** 2,193 `checked_local_query queryN := ⟨mask,
  kind, ownedSet, cert⟩` records (1,821 `.hull`, 326 `.four`, 46 short), using
  `Bridge/SharedLocalQueries.lean`.
  - These are plain S12 `LocalQuery` values, each with `query.Check` by `decide +kernel`.
  - They are used by the Entry domains of C701–C979 (`DirectSingleDomain` lists, checked by
    `Bridge/SmallOwnerDomain(.Three)`), by C983, by C705/716 and (via C979 chunks) by C1092.
  - Each says "no square owns marker group `mask` together with exactly this set of auxiliary
    points". **The HOL Phase-1 `localq.ml` checker applies unchanged.**
- **`Preservation/`**:
  - `Complete/CK.lean` holds the 6 whole-case compositions (§3.1); `All.lean` imports them.
  - `CK.lean` holds the per-case domain-id lists, the owner masks and the `Pending` chain
    (C701, C717, C973, C978, C979; C713's chain is in `Cases/C713/Assembly.lean`).
  - `Chords/` holds the chord stages (§3.5).
  - `HistoricalDictionary.lean` and `InitialBank.lean` are aliases of the C713 dictionary and of
    the `DirectRecipeTable.Bank`.

### 3.7 Volume per historical case

| case | pair stages | plans (with target) | empty plans | `.direct` hints | `.block` hints | initial recipes | overlap groups (point / axis) | explicit axis pair checks | point context checks | (src, nbr) pairs covered | DirectPruning + HistoricalCommon + Cases size |
|---|---|---|---|---|---|---|---|---|---|---|---|
| C701 | 26 | 970 | 413 | 8,801 | 3,500 | 768 | 556 / 297 | 10,624 | 7,662 | 42,189 | 0.6 + 0.39 MB |
| C713 | 9 | 761 | 276 | 6,269 | 3,079 | 1,152 | 159 / 104 | 26,150 | 6,969 | 94,735 | 0.8 + 0.17 MB |
| C717 | 17 | 1,390 | 547 | 12,173 | 5,258 | 1,408 | 350 / 218 | 62,147 | 11,889 | 168,425 | 1.07 + 0.34 MB |
| C973 | 23 | 1,253 | 150 | 11,348 | 5,027 | 704 | 420 / 336 | 27,120 | 8,730 | 73,512 | 0.86 + 0.36 MB |
| C978 | 14 | 628 | 181 | 5,462 | 2,630 | 576 | 243 / 147 | 9,652 | 4,483 | 34,607 | 0.54 + 0.2 MB |
| C979 | 24 | 2,011 | 586 | 18,345 | 7,416 | 1,536 | 316 / 246 | 90,977 | 13,084 | 225,598 | 1.52 + 0.41 MB |
| **total** | 113 | 7,013 | 2,153 | 62,398 | 26,910 | 6,144 | 2,044 / 1,348 | **226,670** | **52,817** | 639,066 | |

Shared across all six:

- 114,465-row / 28,235-pose dictionary;
- 13,269 fan contexts (cycle length ≈ pose rows + block rows, i.e. 6–14 vertices);
- 768 directions;
- 5,645 fan blocks;
- 2,193 local queries;
- 20 chord files (1,298 plans, 2,963 neighbours) and 108 height records.

Each explicit axis check costs 8 directions × (2 cone tests + 1 pair inequality). Each point check
costs 4 face tests.

---------------------------------------------------------------------------------------------------

## 4. C898 (own dictionary; plan type `C898Cached.Plan`)

**Final theorem.** `N12Compact.C898.excludes_case` (`Cases/C898/CompleteCached.lean`).

- It is `family_impossible` → `C898CachedAssembly.mixed_impossible` (`Cases/C898/MixedCached.lean`),
  using 11 owner covers `C898Entry.ownerK_cover` (owner 4, mask 192, is unused).
- `PointPremises` give `ClosedInside (q 4)` at (33/20, 33/20) and (47/20, 33/20).
- The family is `{1,2,12,16,192,768,1056,2048,4096,8192,16384,32768}`, at `RowIdentity.rowAt 485`.

**Chain** (domains `continuousScout898Domain{owner}_{version}`; sizes in brackets):

| step | lemma | S | N | T |
|---|---|---|---|---|
| 0 | `C898Cached.AllPairs.pairStep0_sound` | 1_0 [64] | 8_0 [59] | 1_1 [64] |
| 1 | `pairStep1_sound` | 2_0 [64] | 10_0 [64] | 2_2 [64] |
| 2 | `pairStep2_sound` | 3_0 [64] | 11_0 [59] | 3_3 [64] |
| 3 | `pairStep3_sound` | 6_0 [16] | 3_3 | 6_4 [14] |
| 4 | `pairStep4_sound` | 6_4 | 10_0 | 6_5 [12] |
| 5 | `pairStep5_sound` | 7_0 | 6_5 | 7_6 [63] |
| 6 | `pairStep6_sound` | 7_6 | 11_0 | 7_7 [63] |
| 7 | `pairStep7_sound` | 9_0 | 2_2 | 9_8 [53] |
| 8 | `pairStep8_sound` | 0_0 | 1_1 | 0_9 [61] |
| 9–10 | `C898Chord.Fused.chord_fused` (7 squares; left window with 0_9, 7_7, 11_0, right window with 3_3, 6_5, 9_8) | 5_0 [53] | — | 5_11 [49] |
| 11–13 | `pairStep11..13_sound` | 5_11 → 5_12 [49] → 5_13 [23] → 5_14 [8] | 0_9, 6_5, 7_7 | |
| 14 | `pairStep14_sound` (one common point ⟨10079, 4914, 5000⟩ prunes all 8×53 pairs) | 5_14 | 9_8 | **[]** |

**Dictionary** (`Cases/C898/{SharedRows,SharedPoses,SharedDictionary,SharedDomains,References}.lean`):

- `sparse_rows% "id:x,y,c,strict,denPred"`: 10,851 rows in a 26,026 index space;
- `sparse_poses% 64 26026 "id:angle;rows"`: 2,196 poses in a 3,317 index space, on the 64-angle
  grid only;
- `references : Fin 64 → ReferenceAxis.Reference`, with `references_exact`.

**Entry.** Same machinery as §3.2:

- `EntryDomains`, `EntryRefined`, `EntryPoints` (39 `CertifiedPoint`s), `DirectInitial/Inputs`;
- `RecipeInitial/Batch*` uses `checked_initial_batch`: 704 records (74 empty) giving 1,121 initial
  poses;
- about 605 local queries (484 reused from Phase 1 via `certified_query%`).

**Pair steps** (`CachedPairPlans`, `CachedGeometricPlans`, `CommonPairGroups`, `PairRecords`,
`PairComplements`, `PairFan`, `CachedPairFan`, `CachedCommonPoint`, `CachedPairs/*`;
`Bridge/IndexedCachedPairPlans`, `IndexedRawPairPlans`):

- **Plan** `C898Cached.Plan = ⟨source, block : Option Nat, pieces : List poseId⟩`, written
  literally as `⟨1191, some 0, [1765,1764]⟩` in `StepNNData`.
- `blockRows k` comes from `PairRecords.blockData` (500 blocks of 2–4 rows); `complement` from
  `PairComplements.complementData` (~750 entries).
- **`Plan.Check`:** the contexts are `[poseRows src]` (unblocked) or
  `PairPruning.outsidePieces complement block rows`, i.e. `(¬b_i) :: b_{i−1} … b_1 :: inputs`, the
  "first failing block row" split. Each context must equal the rows of a piece with the same
  angle, and every complement must be `RegionDAG.opposite`.
- **`Plan.sound`:** S \ B ⊆ ⋃ pieces, with pieces as exact sub-poses.
- Pieces are mapped to the target domain by `C898CompactRelaxation.links`: 927
  `cached_relaxation%(dict, src, tgt)` entries in `CompactRelaxation/Data00–14`, macro in
  `Bridge/RelaxationTable.lean`.
  - Hints are synthesised at elaboration by `relaxation_hints%` (`Core/RelaxationSyntax.lean`)
    and re-checked by `RelaxationTable.Entry.Check` (same angle ∧ `RelaxationHints.Check`).
  - So in Lean the hints are **not stored**. A HOL port must re-synthesise them: 1–2-row Farkas
    for every target row.
- **Overlaps.** Same two group kinds as §3.4, but with C898-specific commands:
  - `checked_c898_fan routeN commonRawN := ⟨pose, block, keyAngle⟩ using c898_cycle%(…) |
    c898_entries%(#[…materialize_basis% …])` (`Cases/C898/FusedContextSyntax.lean`). 1,002
    contexts plus 61 for step 14; 256 `cyclicDirections`.
  - `kernel_matrix` for axis groups; common points (201 + 7 + 1).
  - 25,843 (source, neighbour) claims in total, the rest on 354 fallback rectangles.

**Chord 9–10** (`ChordFused*`, `ChordPlans`, `ChordRadii`):

- `central_center_bounds` gives 6397/4000 ≤ cX ≤ 9603/4000.
- Two windows: left `[77541931/5e7, 79616259/5e7]`, right `[252785619/1e8, 25285449/1e7]`.
- 312 `Neighbor` records: two `RowSupport.Check`s each, giving `cX ∈ [lo + r, hi − r]`, hence a
  long vertical section.
- 54 `DirectPlan`s (4 closing) over `cutRows`.
- Soundness via `AngleSection.window_excludes` / `four_vertical_impossible`.

**Volume:** 2.4 MB in 266 files. `audit/C898_COMPACT_ASSEMBLY.md` has the authors' counts.

---------------------------------------------------------------------------------------------------

## 5. Smaller families (no large data)

None of these uses dictionaries, plans or `sparse_*%`. There are two layers:

- **(i) Finite ownership**, all `decide +kernel` over S12 `CertifiedDomain`s:
  - `enumerateAssignments` / `DomainCasesCheck` / `domain_cases_sound`
    (`source/S12/DomainEnumeration.lean`);
  - `feasible (forcedDomains …) = false` → forced owned set (`DomainSearch.lean`,
    `CertifiedDomain.lean`);
  - `Bridge/ForcedAuxiliary` (forced point);
  - `Bridge/{OwnerBudget, RelaxedOwnerDomain, TransformedOwnerBudget, PromotedOwnerBudget,
    CornerPairDomain, UpperMidDomain, SmallOwnerDomain(.Three)}` (relabelled or refined Phase-1
    specs);
  - `Bridge/PrefixCoverage` + `CoverageReorder` (C981 chained prefix tables);
  - `Bridge/FourSquareVectorCover` (dispatch of enumerated ownership vectors to `FourSquareCase` /
    `MidpointCase` recipes).

  All of these are combinatorics on small Finsets of ℕ, best done in HOL as bitmask `num`s.
- **(ii) Hand-written geometry** in `Compact/Geometry`, `Compact/Completion` and top-level
  `Completion/Cases`.

**C981** (`Cases/C981Compact.lean`):

- The contract is `ExcludesVector v` for the 117 `representativeVectors`
  (`Completion/Cases/C981/VectorData.lean`).
- Coverage `complete_vector_coverage : DomainCasesCheck domains coveredVectors`:
  - 12 domains (`OwnershipDomains.lean`; C976 `DirectSingleDomain`s from
    `Bridge/C981DomainReuse/Subset` with 202 `checked_local_query` records in
    `Bridge/C981DomainReuse/Queries00–08`);
  - a `PrefixCoverage.Chain` of 12 `StepCheck`s by `rfl` (`Completion/Cases/C981/Coverage/Prefix*`,
    ~10.2k partial vectors, ~400 KB);
  - the result lands in 234 vectors (117 + transposes).
- `diagonal_ownershipVector` handles the transpose symmetry.
- The 117 representative proofs are hand geometry, registered in `Cases/C981Registry.lean`
  (`Bridge/C981*`, `Compact/Completion/C981/*`, `Cases/C981V116.lean`).
- A HOL port can replace the prefix chain by one DFS over 12 bitmask domains that checks
  membership in the 234 vectors (the chain itself is untrusted data).

**C1092** (`Cases/C1092Compact.lean`):

- `C1092WallSymmetry.original_four_branches` (16 sign patterns, 8 D4 symmetries, decided)
  reduces to 4 canonical branches with hand endings:
  - `C1092MPPM.windmill`;
  - `C1092MMMPTwoFifthsEntrance.branch_ending`;
  - `C1092MMMM.adjacentPair`;
  - `C1092OppositePair.oppositePair`.
- These are all in `Compact/Completion/C1092` (364 files, 2.6 MB).
- The only data dependency: `Bridge/C1092AuxiliaryCover` uses `single979_5_1` and `single979_8_1`
  from `Cases/C979/EntryQueryChunks/Chunk11,17`, i.e. the HistoricalOwnership queries.

Smaller ownership volumes (each ≤ 10 domains, ≤ ~50 allowed sets):

- MergedLower: 4 families × 9 domains, 12 recipes;
- Endpoint684: 9 domains, 6 patterns;
- C849851: 20 feasibility checks;
- MergedTopFurther: 30;
- OppositeCentralWalls: 48;
- C868 and C84: a handful.

---------------------------------------------------------------------------------------------------

## 6. Compact/Core, file by file

`[n]` is the number of direct importers. "Hist" = historical cases (§3).

| file | role | used by |
|---|---|---|
| `IntegerSupport` | `Row`, `Row.Holds`, `Row.normalized` + `normalized_holds_iff`; `TwoRow.Check` (w_l·a + w_r·b = s·t, signs, strictness) + `TwoRow.Check.sound` — **base Farkas lemma** | everything |
| `SparseInteger` | `Terms`, `sum`, `Certificate ⟨terms, scale⟩`, `Certificate.Check.sound` (n-term nonnegative integer combination = scale·target), `refutes`, `replay` (topological DAG of derived rows) | RowSupport, EmptyContext, RelaxationHints |
| `PairSupport` | 4-variable target `Target ⟨x,y,c⟩` (eval p q = x·(p₀−q₀)+y·(p₁−q₁)+c), `cramer a b x y`, `Weights.Check.sound` | VertexSupport, RowSupport |
| `PairSupportFast` | Cramer identities proved once; `FastCheck` | PairSupport users |
| `RowSupport` | `one = 1>0`; `RowSupport.Check a b t` = Cramer weights + slack on `one`; `sound` | RelaxationHints, IndexedRelaxation, C898 |
| `RelaxationHints` | `Hint = constant/copy/single/pair`, `Check sources targets hints` (one hint per target, in order), `sound` | BlockedTarget, IndexedChord, RelaxationTable, DirectPruningPlan |
| `EmptyContext` | `Witness ⟨inputs, terms⟩`: nonnegative combination with zero linear part and negative (or ≤0 strict) constant → False | BlockedTarget, IndexedCommonGroups, DirectPruningPlan |
| `RegionDAG` | only `opposite` (exact strict complement row) and `opposite_holds` are used; the DAG replay itself is unused | BlockedTarget, PairPruning, DirectPruningPlan |
| `BlockedTarget` | `Hint = direct/block/impossible`, `Check`, `sound`, `source_sound` (§3.3) | IndexedBlockedTarget (hist) |
| `VertexSupport` | `Basis ⟨first, second, x, y, den⟩`, `Basis.Check` (vertex on both rows), `Cone` (Cramer weights ≥ 0), `bound`, `Basis.sound` (n·p ≥ n·v on the cone), `PairCheck`, `pair_sound` | all fan/pair/point checks |
| `VertexFromRows` | `Basis.fromRows(Primitive)` (intersection of two rows, gcd-reduced) and its check | BoundaryFan |
| `VertexFanTable` | `RawContext ⟨inputs, reference, entries⟩`, `RawContext.Check` (memberships + vertex equations), `certify` | BoundaryFanSyntax |
| `CachedSupportFan` | certified fan entries, `select`, `scale`, `target_factor`, `PairCheck`, `pair_sound`; `Context.numeric(_valid)` | RawSupportFan, C898 |
| `RawSupportFan` | proof-free numeric fan, binary-search `select`, `ValidFor`, **`PairCheck` (8-axis)** + `pair_sound` | hist, C898 |
| `RawSupportFanBool` | Boolean replay of the same check (`check_sound`) | RawSupportFan users |
| `RawSupportFanBridge` | erasure lemmas between cached and raw fans | C898 |
| `SupportFan` | older fan with explicit breakpoints (`AxisCheck`) | C898 only |
| `DirectionalSupportCache` | `Datum` (one support bound per context/key) + `Datum.Check`, `pair`, `Table`; used by CommonPoint | CommonPoint |
| `CommonPoint` | `Point ⟨x,y,den⟩`, `axis`, `check`, `inside_sound` (§3.4) | IndexedCommonPoint (hist), C898 |
| `ReferenceAxis` | integer `Reference`, `Direction`, `radiusNumerator`, `target`, `directions a b` (8 axes), `target_exact`, **`overlap`** (bridge to `S12.axisOverlapForms_sound`) | RawSupportFan, C898 |
| `PairPruning` | `inputs_hold` (normalized → integer rows), `actual_overlap`, `outsidePieces` (C898) | hist, C898 |
| `PlanarVertex` | `BoxNormals`, `Feasible`, `VertexBound`, **`nonnegative_of_vertices`** (vertex enumeration lemma) | PlanarVertexCheck |
| `PlanarVertexCheck` | exact integer `vertex a b`, `PairCheck`, `Check`, `Check.sound` | DirectPoseCover, VertexCutRelaxation |
| `PlanarVertexSparse` | `triangle` (unordered pairs), `UnorderedCheck`, `SparseCheck`, witness variants | initial recipes, C713 height |
| `PlanarBoundaryFilter` | `LineExclusion` (a parallel base row proves a line is infeasible), `FilterCheck`, `active` | initial recipes |
| `PlanarBoundaryHints` / `PlanarBoundaryAuto` | cached and auto-discovered line exclusions | initial recipes |
| `CoordinateBound` | rows `x ≥ b`, `x ≤ b` from a rational b (`lower`/`upper`) | AxisSection, C898 chord |
| `KernelMatrix` | `kernel_matrix name : m × n => P` command: `Range` chunks of 8 by `decide +kernel` + balanced `Range.append` | HistoricalCommon groups, C898 |
| `FiniteCheckChunks` | `Check claim block` / `sound` (blocks of 8) | C898 CompactRelaxation |
| `FiniteKernelDecision` | tactic macro `split_kernel_check` (fin_cases + `decide +kernel`) | C717/C979 EntryQueryChunks, C705716 |
| `SparseLiteral` | `Tree`, `lookup`, `sparse_rows%`, `sparse_poses%`, `sparse_rows_subset%` | HistoricalData, C898 |
| `BoxRowRecipe` / `BoxRowSyntax` | `B:` box lines → 4 rows; `boxed_sparse_rows%` | HistoricalData |
| `StripRowRecipe` / `StripRowSyntax` | `M:` / `P:` strip lines → 2 parallel rows; `strip_sparse_rows%` | HistoricalData (50 files) |
| `RowSyntax` | `row_array%`, `row_chunks%`, `row_text%` literals | C898 DirectInitial |
| `PoseSyntax` | `pose_text%` | C898 |
| `FormSyntax` / `RowMaterializeSyntax` / `BasisMaterializeSyntax` | `materialize_forms%`, `materialize_rows%`, `materialize_basis%` (definitional reduction to literals; the caller re-proves equality) | Bridge, C713 HeightData, C898 |
| `BoundaryFanSyntax` | `BoundaryFan.context` (cycle → vertex entries), `materialize_boundary_fan%`, `materialize_raw_fan%` | HistoricalCommon, C898 |
| `BoundaryHintSyntax` | `boundary_plan%`, `boundary_rows%`, `boundary_cache%` (untrusted line-exclusion search) | DirectCachedRecipe |
| `RelaxationSyntax` | `relaxation_hints%`, `cached_relaxation%` (untrusted hint synthesis) | C898 CompactRelaxation |
| `Dag`, `DirectLinear`, `LinearCombination`, `IntegerSupportCase` | **not in the closure of Final** | — |

**Irreducible soundness facts.** Everything above reduces to these:

- (F1) the integer Farkas combination (`SparseInteger.Certificate.Check.sound` /
  `TwoRow.Check.sound`);
- (F2) `opposite_holds` plus the first-failing-row split;
- (F3) the vertex-cone support bound (`VertexSupport.Basis.sound`), a special case of F1;
- (F4) SAT via `ReferenceAxis.overlap` ← `S12.axisOverlapForms_sound`;
- (F5) `CommonPoint.inside_sound`;
- (F6) `PlanarVertex.nonnegative_of_vertices`.

Everything else is lookup, materialization or bookkeeping.

---------------------------------------------------------------------------------------------------

## 7. Bridge (non-FourSquare) modules needed

**Historical/C898 certificate path:**

| module | role |
|---|---|
| `IndexedRelaxation` | `Dictionary`, `pose`, `transfer`, `Link`, `cover_sound` |
| `IndexedBlockedTarget` (+ `Syntax`) | §3.3 plan / stage / `BlockOverlap` / `step_sound`; `checked_blocked_batch` |
| `DirectPruningPlan` | `outsideRows` split, `Branch` (`keep` / `close`) — used by chord and CommonGroupPruning |
| `IndexedCachedPairPlans`, `IndexedRawPairPlans` | `PoseContext` (pose + block + fan), `PairCheck`, `pair_sound`, `block_forbidden`, C898 `Plan` / `StepCover` / `step_sound` |
| `IndexedCommonPoint`, `IndexedCommonGroups`, `CommonRectanglePartition`, `CommonGroupPruning`, `CommonHeaderPruning` | §3.4 overlap groups and their binding to plan headers |
| `IndexedCommonContext`, `CheckedCommonContext`, `CheckedCommonFanCommand`, `CheckedCommonGroup` | context and group commands |
| `HistoricalPoseFanRecipe` | `reference` of an AngleEnclosure as an integer `Reference` |
| `RelaxationTable` | C898 `cached_relaxation%` links |
| `DirectPoseCover`, `DirectPoseForms`, `DirectOwnerRecipe`, `DirectCachedRecipe`, `DirectRecipeTable`, `DirectRecipeCheck`, `DirectRecipeDictionary`, `CheckedRecipeCommand`, `InitialCoverBatch`, `DirectOwnerFamily`, `PointPremises` | §3.2 initial covers |
| `SharedLocalQueries` | `checked_local_query`, `certified_query%` |
| `SmallOwnerDomain`, `SmallOwnerDomainThree` | `DirectSingleDomain` checks against local queries (Entry domains) |
| `AngleSection`, `AxisSection`, `IndexedChord`, `ChordSyntax`, `ChordPacking` | §3.5 chord |
| `VertexCutRelaxation`, `OccupiedRowChord` | C713 height stage |

**Small families:** `ForcedAuxiliary`, `OwnerBudget`, `RelaxedOwnerDomain`,
`TransformedOwnerBudget`, `PromotedOwnerBudget`, `CornerPairDomain`, `UpperMidDomain`,
`PrefixCoverage`, `CoverageReorder`, `FourSquareVectorCover`, `MidpointCase`,
`EndpointHighRightCase`, `OwnerSegmentCrossing`, `CongruentSAT` (theorem), plus the hand-proof
files `C84*`, `C696*`, `C977*`, `C981*` (including `C981DomainReuse/*` with 202 queries), and
`C1092*` / `C1092WallSymmetry/*`.

**Not needed:** `BorderEndpoint`, `C977DisjointChain`.

---------------------------------------------------------------------------------------------------

## 8. What to implement once in HOL

### 8.1 Semantics (port faithfully)

- **`Row`.** `row_holds (x,y,c,s) (px,py) = if s then &0 < x*px+y*py+c else &0 <= …` over
  integers cast to real. The dictionary is a function or array from index to row.
  `normalized` (÷den) can be dropped if the HOL pose definition uses the integer rows directly.
  Then prove one lemma that HOL's pose equals the S12 pose: equal for den > 0.
- **`AngleEnclosure`.** Fields, `Check` (quadratic interval checks: port
  `S12.QuadraticInterval.CheckOn`), and `outer_sound` / `inner_sound` / `wall_sound`. The 192
  enclosures are in `source/S12/AngleData64/128.lean`.
- **`PoseLeaf`**, `Realizes`, `AngleWitness`, `OrientedRealizes`, `OrientedPoseCovered`, and
  `transfer` (same angle and target rows hold at the centre ⇒ OrientedRealizes).

### 8.2 Six generic soundness theorems

- **(F1) 2-D integer Farkas.**
  - Statement: if `∀i∈I. row_holds r_i p`, `w_i ≥ 0`, `s > 0`, and Σ w_i·(x_i, y_i, c_i) =
    s·(x_t, y_t, c_t) + (0, 0, slack) with `slack ≥ 0`, and the strictness rule holds (target
    strict ⇒ some w_i > 0 on a strict row, or slack > 0 via `1 > 0`), then `row_holds t p`.
  - The contradiction form is the target `0 > 0` (EmptyContext).
  - This covers `TwoRow`, `RowSupport`, `RelaxationHints` (constant/copy/single/pair),
    `EmptyContext`, `Branch.close`, chord neighbour bounds and C898 links.
  - Checker: compute the Cramer weights in OCaml and check the integer identities by numeral
    arithmetic.
- **(F2) Complement split.** `row_holds (opposite r) p ⇔ ¬row_holds r p`, and
  `¬(∀ b∈B. holds b) ⇒ ∃i. holds(opposite b_i) ∧ ∀ j<i. holds b_j`. This gives the plan lemma:
  for each target row τ, S ⇒ τ, or S ∧ ¬τ ⇒ B (F1 on `opposite τ :: S`); hence
  `S ∧ ¬B ⇒ T`.
- **(F3) Directional support.** If basis rows a, b (both in region R) meet at the vertex
  v = (vx, vy)/den and n = λa_n + μb_n with λ, μ ≥ 0 (Cramer), then
  `∀p∈R. n·p ≥ n·v` (strict if a strict row has a positive weight). This is F1 with 2 rows.
- **(F4) SAT for rational reference squares.** For reference squares A, B (rational c, s with
  c²+s² = 1 and side > 0) at centres p, q: if the 8 gap inequalities
  `n·(p−q) + r_A(n) + r_B(n) > 0` hold for n ∈ {±u_A, ±u_A^⊥, ±u_B, ±u_B^⊥}, then the open
  squares intersect.
  - Lean: `S12.axisOverlapForms_sound` (`source/S12/AxisOverlapCertificate.lean`, which uses
    `ConvexOverlap`, `AxisGap`, `AxisAlgebra`).
  - The HOL project may already have an equivalent from Phase 1 (`hull.ml`) or
    `geometry/CongruentSAT.ml` (that is the congruent-square version).
  - Combined with inner-reference containment (`Realizes`) this gives the real squares
    overlapping, which contradicts the disjointness hypothesis.
- **(F5) Common point.** If for the 4 own directions u_i of A, `u_i·(P − c) < side_A/2` for all
  c ∈ R_A (via F3 lower bounds on u_i·c), then `P ∈ A + c ⊆ q`.
- **(F6) Planar vertex enumeration.** Region F = closed base polygon (containing the box normals)
  minus open convex blocks. If every target row is ≥ 0 at every feasible pairwise line
  intersection, then it is ≥ 0 on F.
  - Lean proof: `Core/PlanarVertex.lean`, about 11 KB, an elementary two-line-walk argument.
  - Needed only for the ~6.8k initial-cover recipes and the 108 C713 height records.
  - Alternative avoiding F6: replace each recipe by an explicit case split. Choose one failing
    face per forbidden block, check F1 per convex piece, and use OCaml to prune infeasible
    combinations with F1 contradictions. This is exponential in the number of outside points in
    the worst case, so F6 is the safer investment.

Plus the fixed geometric lemmas, already ported or being ported:

- `four_on_one_cut` / `horizontal_long_section` / `oriented_section` / `Radius.bound` (chord);
- `OccupiedRow.above_radius` (C713);
- `PointPremises.sound` / `CertifiedDomain` / `LocalQuery.Check` (Phase-1 style).

### 8.3 Recommended HOL representation and checker strategy

- **Don't port the Lean caches.** Fans, binary-search keys, `directions` arrays, materialized
  literals, `KernelMatrix` chunking and `RectanglePartition` are all untrusted acceleration.
  - The pair overlap obligation is simply ∀ i < u, j < v: `PairOverlaps(src_i, nbr_j)`.
  - An OCaml oracle can recompute, per (context, direction), the support vertex by enumerating
    the polygon's vertices. A context has ≤ 14 rows, so at most 91 candidate pairs.
  - It then emits F3 instances.
- **Cache support facts per (context, direction).** The direction set is determined by the
  angles: 4 own normals per angle, 192 angles, so 768 directions. Each support bound
  `n·c ≥ m(context, n)` can be proved once and reused across all pairs. This is exactly
  `Core/DirectionalSupportCache`.
  - A pair check then becomes 8 rational comparisons
    `m_A(n) + m_B(−n) + r_A(n) + r_B(n) > 0` (with `r` from the two angle references).
  - Number of support facts ≤ 13.3k contexts × (4 + 4·#neighbour angles) ≈ a few ×10^5–10^6.
    Alternatively, use F4 directly with a 4-variable F1 certificate per pair and axis
    (~1.8M + C898's ~0.2M small certificates).
- **Prefer a reflective checker.** Define a HOL function `check_plan`, `check_pair`, … on lists
  of integer triples, prove it sound against F1–F6 once, and evaluate it with `computeLib`
  (memory note: build compsets in the main domain; evaluation per domain) or a custom
  `NUM_REDUCE`/`INT_REDUCE`-based conversion.
  - The arithmetic is integer only: inputs ≤ ~2^54, products ≤ ~2^120.
  - The C898 relaxation hints and the historical `.block` / `.direct` hint lists can be
    regenerated by OCaml search instead of parsed. The plans, blocks and targets must be parsed,
    because they define the case structure.
- **Parsing.** All data are text inside Lean strings or constructor syntax:
  - `id:x,y,c,b,d` / `B:` / `M:` / `P:` lines in `HistoricalData/RowsChunks`;
  - `id:angle;rows` in `PosesChunks` and `SharedFanBlocks`;
  - `planN (src,block,tgt) [hints]` in `DirectPruning`;
  - `checked_common_fan …` in `HistoricalCommon/Bindings*`;
  - `checked_*_group …` plus the partition trees in `HistoricalCommon/CK`;
  - `checked_initial_batch` records;
  - `checked_chord_*` records.

  A Python extractor in the style of `n12/scripts/fs_extract.py` can dump everything to compact
  JSON. Box and strip decoding is defined in `Core/BoxRowRecipe.lean` and
  `Core/StripRowRecipe.lean` (`Bound.row`, `Strip.row`).

---------------------------------------------------------------------------------------------------

## 9. Data volume and feasibility summary

| object | count | per-item work |
|---|---|---|
| historical dictionary rows / poses | ~99.5k present (114,465 ids) / ~12.7k+ (28,235 ids) | parse |
| historical pruning plans | 7,013 with target, 2,153 empty | ~13 target rows each: F1 (1–2 rows) or F2+F1 |
| target-row hints | 62.4k direct + 26.9k block | 1 Cramer 2×2 + identity check |
| historical fan contexts | 13,269 | ≤ 14 vertices; F3 per used direction |
| historical axis pair checks | 226,670 pairs × 8 axes | 3 integer tests per axis (or cached support sums) |
| historical point checks | 52,817 contexts × 4 faces | 1 cone + 1 inequality each |
| (src, nbr) pairs logically needed | 639,066 (hist) + 25,843 (C898) | covered by groups; a HOL version may use point groups or axis checks freely |
| initial recipes (vertex enumeration) | 6,144 (hist) + 704 (C898) | O(L²) vertex tests, L ≈ 20–40 lines |
| chord plans / neighbours | 1,298 / 2,963 (hist) + 54 / 312 (C898) | 2 branches of F1, plus a radius quadratic check per angle |
| C713 height records | 108 | vertex enumeration |
| local queries (HistoricalOwnership + C898 + C981 + C976) | 2,193 + ~605 + 202 | existing `localq.ml` |
| C898 links / plans / contexts | 927 / 601 / 1,063 | as above |

**Conclusion.**

- The largest single item is about 2M directional integer tests (~10^7 bignum multiplications).
  As a proved-sound HOL checker evaluated by conversion this is hours on one core; with the
  existing 90-domain parallel setup it is tens of minutes.
- Building per-inequality theorems with `REAL_ARITH` would be orders of magnitude slower.
- Recommended order:
  1. F1/F2 plus plan stages (cheap, 7k plans);
  2. F3/F4/F5 plus overlap groups (dominant cost);
  3. F6 plus initial covers;
  4. chords;
  5. C898 (same components, own dictionary).

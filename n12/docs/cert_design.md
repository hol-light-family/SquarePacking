# Certificate checker design (HOL Light port of the 7 certificate cases)

This document describes the HOL side of the seven certificate cases: representations, statement
shapes, the reflective-checker technique and the data formats.  It is a companion of
`jatloe_cert_map.md`, the map of the Lean machinery; "map §x" below refers to its sections.

Cases: 701, 713, 717, 973, 978, 979 ("historical", shared dictionary) and 898 (own
dictionary). Final per-case deliverable: `|- EXCLUDED_ROW ri` (n12/phase1/step6.ml) for the
row `ri` of the case.

---------------------------------------------------------------------------------------------

## 1. Principles

1. **Statements are faithful, checking is free.** Every HOL theorem that leaves the
   certificate layer (the case theorem `EXCLUDED_ROW ri`) mentions only the Phase-1 packing
   (`NPACK`, `FFP`, `ROW_LIST`). All intermediate objects (dictionary poses, plans, headers)
   are internal HOL definitions; they only have to be *true*. Each intermediate statement is
   nevertheless a direct translation of its Lean counterpart (comment `(* Lean: ... *)`).
2. **Untrusted search, kernel checking.** Python/OCaml may extract, search and pre-compute
   (Cramer weights, support vertices, partitions, ...). Every numerical claim is checked by
   the HOL kernel, either by a proved-sound *reflective checker* evaluated by conversion
   (§5) or by ordinary proof. No `CHEAT_TAC`, `new_axiom`, `mk_thm`.
3. **Do not port Lean caches** (map §8.3): materialized literals, `kernel_matrix` chunking,
   binary-search keys, `RectanglePartition`s are acceleration only. Port the *checks*.
4. **One representation per concept**, defined once in `n12/cert/`. Tags: `CR_`/`cr_`
   (core, this doc); each layer has its own prefix (`OV_`, `PV_`, `CH_`, `EN_`, `C8_`, `CA_`).

---------------------------------------------------------------------------------------------

## 2. Core representation (n12/cert/CR_Row.ml, implemented)

| Lean | HOL |
|---|---|
| `IntegerSupport.Row ⟨x,y,constant,strict⟩` | `CRow (x:int) (y:int) (c:int) (s:bool)` : `crow`; accessors `cr_x cr_y cr_c cr_s` |
| `Row.eval r p` | `cr_eval r px py = real_of_int(cr_x r)*px + real_of_int(cr_y r)*py + real_of_int(cr_c r)` |
| `Row.Holds r p` | `cr_holds r px py <=> if cr_s r then &0 < cr_eval r px py else &0 <= cr_eval r px py` |
| `Row.normalized r den` | `cr_normalized r den` (lincon with coefficients `/ &den`); `CR_NORMALIZED_HOLDS_IFF` (`0 < den`) |
| (den = 1) | `cr_lincon r` (lincon with integer coefficients); `CR_LINCON_HOLDS` |
| `RegionDAG.opposite` | `cr_opposite r = CRow (--x) (--y) (--c) (~s)`; `CR_OPPOSITE_HOLDS` |
| a dictionary pose `(poseAngle i, poseRows i)` | `CPose (a:num) (rows:crow list)` : `cpose`; `cp_angle`, `cp_rows` |
| `Dictionary.pose i : PoseLeaf` | `cr_leaf p = PoseLeaf (s12_angles (cp_angle p)) (MAP cr_lincon (cp_rows p))` |
| the same with Lean's denominators | `cr_dict_leaf a rds`; `CR_LEAF_NORMALIZED`: realizes/oriented-realizes are equivalent |
| `Dictionary.transfer` | `CR_TRANSFER` (same angle index, target rows hold at the centre) |
| `PoseLeaf.Realizes`, `OrientedRealizes`, `OrientedPoseCovered` | certlib: `pose_realizes`, `oriented_realizes`, `oriented_pose_covered` (n12/certlib/README.md) |
| `C713Shared.angles : Fin 192 → ...` | certlib `s12_angles` (`S12_ANGLES_CHECKED : forall i. i < 192 ==> ae_check (s12_angles i)`) |
| `C898` angles (64-grid only) | `EL a angles64` — C898 uses its own `cpose`-like constructor or `s12_angles a` with `a < 64` (identical for a < 64) |

Points are two reals `px py`; "at the centre of q" means
`cr_holds r (lcx c s u v a) (lcy c s u v a)` for the square `c s u v a`.

**Denominators are dropped.** Lean's poses use `Row.normalized (denPred+1)`. HOL poses use
the integer rows directly (`cr_lincon` = denominator 1); `CR_LEAF_NORMALIZED` proves that the
pose semantics are unchanged. Extractors still output `denPred` (for audit), checkers ignore it.

**Angle index range.** `CPose a rows` with `a >= 192` would be meaningless (`s12_angles`
is unspecified there); every overlap/entry prover needs `a < 192` (`ae_check`), which is
checked by evaluation (`NUM_LT_CONV`) of the literal index. The extractor asserts it.

### 2.1 Dictionary as OCaml tables, domains as HOL constants (n12/cert/CR_HistData.ml)

The whole 114,465-row dictionary is never one HOL term, and individual poses are **not**
HOL constants (12.7k constants would slow every `mk_const`/parse, the constant table is an
association list). Instead:

- **Row terms**: OCaml `cr_row_tm id : term` (memoized) builds `CRow (&x) (-- &y) ...` from
  `n12/data/cert/hist_rows.txt`. Integer literals are `&n` / `-- &n` (`mk_intconst`). Missing ids
  give Lean's fallback row `CRow (&0) (&0) (&0) F`.
- **Pose terms**: OCaml `hp_tm id : term` (memoized) = `CPose a [cr_row_tm r; ...]`
  (missing ids: Lean's fallback `(0, [])`). Row and pose terms are physically shared, so
  equal poses are `==` and `aconv` is O(1) on them.
- **Domain constants**: `h<case>_d<owner>_<version>` (e.g. `h713_d0_1`), made by
  `hdom_def (case, "0_1")` : `|- h713_d0_1 = [CPose ..; ...]` (Lean
  `continuousScout713Domain0_1Ids`, in Lean's order), type `cpose list`. The Lean
  `List PoseLeaf` domain `continuousScout713Domain0_1` is `MAP cr_leaf h713_d0_1`.
  C898: `c898_d<owner>_<version>` (same scheme, own tables).
- **Header constants**: `h<case>_s<step>_hdrs : (cpose # (crow list) option) list`
  (`ck_hdrs_tbl (case, step)` holds the definition), one entry per plan in plan order.
- **Every layer builds row/pose/domain terms only through these functions** (it loads
  `CR_HistData.ml` and never re-defines the domain constants), so that terms of different
  stages and layers are syntactically identical and theorems compose by
  `MP` without conversions. Build all terms in the main domain before parallel work (the
  memo tables are not domain-safe).

---------------------------------------------------------------------------------------------

## 3. F1/F2 checkers (n12/cert/CR_Farkas.ml, CR_Plan.ml, implemented)

| Lean | HOL definition | soundness |
|---|---|---|
| `TwoRow.Check` | `cr_tworow_check wl wr sc a b t` | `CR_TWOROW_SOUND` |
| `SparseInteger.zero`, `sum`, `Nonnegative` | `cr_zero`, `cr_sum rows terms`, `cr_nonneg` (rows = list, read by `cr_rowat`) | `CR_SUM_SOUND` |
| `Certificate.Check` | `cr_cert_check terms scale rows t` | `CR_CERT_SOUND`, `CR_CERT_SOUND_ALL`, `CR_REFUTES` |
| `PairSupport.cramer` | `cr_cramer a b x y` | (data only) |
| `RowSupport.one`, `RowSupport.Check` | `cr_one`, `cr_rs_check a b t` | `CR_RS_SOUND` |
| `RelaxationHints.rowAt`, `SingleCheck`, `ConstantCheck` | `cr_rowat`, `cr_single_check`, `cr_const_check` | `CR_SINGLE_SOUND`, `CR_CONST_SOUND` |
| `RelaxationHints.Hint` / `.Check` / `Check` | `crhint = RhConst / RhCopy i / RhSingle i / RhPair i j`; `cr_hint_check`, `cr_hints_check` | `CR_HINT_SOUND`, `CR_HINTS_SOUND` |
| `EmptyContext.Witness.Check` | `cr_empty_check rows inputs terms` | `CR_EMPTY_SOUND` |
| `BlockedTarget.Hint` / `.Check` / `Independent` / `Check` | `cbhint = BhDirect h / BhBlock hs / BhImpossible ins terms`; `cr_bhint_check`, `cr_bhint_indep`, `cr_bt_check` | `CR_BHINT_SOUND`, `CR_BT_SOUND`, `CR_BT_SOURCE_SOUND` |
| `IndexedBlockedTarget.Plan` / `.Check` | `cplan = CPlan src (blk:(crow list)option) (tgt:cpose option) hints`; `cr_plan_check` (`CR_PLAN_CHECK_LEAN` restates it in Lean's form) | `CR_PLAN_SOUND` |
| `Plan.header` | `cpl_header p = (cpl_source p, cpl_block p)` | |
| `Stage.Check` | `cr_stage_ok S T plans` (S, T : `cpose list`) | |
| `Stage.BlockOverlap` | `cr_block_overlap headers N` | |
| `PairTransition` | `cr_pair_transition S N T` (S N T : `pose_leaf list`) | `CR_STAGE_SOUND`, `CR_STAGE_THM` |
| `PairPruning.outsidePieces` (F2 first-failing-row split) | `cr_outside_pieces block inputs` (rows, complement = `cr_opposite`) | `CR_OUTSIDE_PIECES_SOUND` |
| `RelaxationTable.Entry.Check` / `cover_sound` (C898 links) | `cr_relax_check src tgt hints` | `CR_RELAX_SOUND`, `CR_RELAX_COVER_SOUND` |
| `IndexedCommonGroups.PairOverlaps` | `cr_pair_overlaps src blk n` | `CR_BLOCK_OVERLAP_OF_PAIRS` |

All checking functions are *total executable* HOL functions over `int` literals, `num`
indices, lists, options and booleans; the hint indices are positions in the source list
(as in Lean, not dictionary ids). The Cramer weights are *recomputed* by the checker
(`cr_cramer`), exactly as in Lean, so plan data = Lean hint lists verbatim.

---------------------------------------------------------------------------------------------

## 4. Statement shapes (fixed)

Notation: a square is the 5-tuple; `UNIT(c,s,a)` abbreviates
`c * c + s * s = &1 /\ &0 < a`; `SIDE(a)` abbreviates `&1 < a /\ a <= &1001 / &1000`.
`cov D q` abbreviates `oriented_pose_covered (MAP cr_leaf D) cq sq uq vq aq`.

### 4.1 Pair stage (DirectPruning StepNN) — this layer

```
CK_STAGE.(NN) : |- cr_block_overlap hCK_sNN_hdrs (MAP cr_leaf hCK_dB_v)
                   ==> cr_pair_transition (MAP cr_leaf hCK_dA_v) (MAP cr_leaf hCK_dB_v)
                                          (MAP cr_leaf hCK_dA_w)
```
where `hCK_sNN_hdrs` is a constant `= [(CPose .. [..], NONE); (CPose .., SOME [CRow ..;..]); ...]`
(one entry per plan, in plan order; empty plans have `SOME []`; definition theorem in
`ck_hdrs_tbl (case, step)`) and the domains are the
Lean `Stage` fields `⟨sources, neighbors, targets⟩`. Produced by `CR_STAGE_SOUND` from
per-plan `|- cr_plan_check (CPlan ...) <=> true` (evaluated, §5), the literal equality
`MAP cpl_source plans = S` and the `MEM` facts for targets (by a structural rule, no
evaluation). OCaml table: `ck_stage_thm (case, step)`.

### 4.2 Block overlaps (F3/F4/F5 workers; map §3.4)

Goal per stage: `|- cr_block_overlap hCK_sNN_hdrs (MAP cr_leaf hCK_dB_v)`.
Recommended reduction (lemma `CR_BLOCK_OVERLAP_OF_PAIRS`, implemented in CR_Plan.ml):
```
cr_pair_overlaps src blk n <=>
  forall cq sq uq vq aq ct st ut vt at. UNIT(q) /\ UNIT(t) /\
     pose_realizes (cr_leaf src) q /\ (forall r. MEM r blk ==> cr_holds r (lcx q) (lcy q)) /\
     pose_realizes (cr_leaf n) t
     ==> exists x y. linside q x y /\ linside t x y
(forall src blk n. MEM (src, SOME blk) hdrs /\ MEM n Nposes ==> cr_pair_overlaps src blk n)
  ==> cr_block_overlap hdrs (MAP cr_leaf Nposes)
```
(`pose_realizes` suffices; it is implied by `oriented_realizes`.) The pair obligations are
discharged by reflective checkers for:
- **F3** support bound: rows a, b of a region R meeting at v; cone weights ≥ 0 ⇒
  `n·p ≥ n·v` on R (a 2-row `cr_tworow_check` with target the direction row).
- **F4** SAT for rational reference squares: certlib `AOC_AXISOVERLAPFORMS_SOUND` /
  `axis_overlap_forms` with inner reference squares `ae_reference w (&1)` (`AR_INNER_SOUND`);
  together with `pose_realizes` (inner reference ⊆ q) this gives the overlap.
- **F5** common point: 4 support bounds ⇒ P in the inner reference square of both.

The OCaml oracle chooses per pair either a common point (group of pairs sharing P) or the
8-axis check, recomputing support vertices by vertex enumeration of the ≤ 14-row polygon
(no Lean fan/partition data needed, but `HistoricalCommon` group data may be used as hints).
Cache per (context, direction) support facts `|- forall p. region rows p ==> n·p >= m` and reuse.

### 4.3 Initial covers (F6 + Entry roots; map §3.2)

Geometric part (worker F6):
```
CK_INITIAL.(k) : |- forall c s u v a. UNIT(c,s,a) /\ SIDE(a) /\ lcont c s u v a /\
                     linside c s u v a x1 y1 /\ ... (insideK, rational literals) /\
                     ~linside c s u v a x1' y1' /\ ...  (outsideK)
                     ==> oriented_pose_covered (MAP cr_leaf hCK_dk_0) c s u v a
```
(Lean `DirectPoseCover.Owner.oriented_sound` + `ownerK_leaves_shared`). Checker:
`PlanarVertexCheck.Check` (F6) ported as a reflective function over `crow` lists, plus
`Root.Check` side conditions (`BoxNormals`, `poseInputs`/`poseForbidden` membership via certlib
`pose_inputs`/`pose_forbidden`, `strictOK`), plus `covers_interval (&0) (&1)` of the root
angles (certlib `ANGLES64_COVER`/`ANGLES128_COVER`). Note `poseInputs` rows are *rational*
lincons; prove once that `cr_lincon r` (or `cr_normalized r d`) equals the certlib lincon of the
form (by `REAL_RAT_REDUCE_CONV`), or state the root check on integer rows obtained by
clearing denominators (Lean `Form.row`).

Packing part (worker ENTRY): the premises of `CK_INITIAL.(k)` for the square owning mask
`maskK` follow from the ownership domain (Lean `CertifiedDomain` built from local queries,
`PointPremises.Check`). This extends `n12/geometry/gen_bridge.ml` (which handles *forced*
owned sets) to domains with several allowed owned sets (all of them must contain the
inside points / exclude the outside points). Local queries: Phase-1 `localq.ml` checker.

### 4.4 Chord stages (map §3.5) and C713 height

```
CK_CHORD.(NN) : |- forall q0 q1 q2 q3. (each) UNIT(qi) /\ &1 < a_i /\ lcont qi /\
                    (pairwise, i<j) ldisj qi qj /\
                    cov Dsrc q0 /\ cov N1 q1 /\ cov N2 q2 /\ cov N3 q3
                    ==> cov Dtgt q0
```
(Lean `Preservation.Chords.CKStepNN.sound`, `Fin 4 → OpenSquare`; `ldisj` both orders are
derivable by symmetry, state `i<j` only.) Checker: `IndexedChord.Plan.Check`
(two `DirectPruningPlan.Branch` = F1 keep/close) + `Neighbor.Check` (F1) + `Radius.Check`
(quadratic on the angle interval, certlib `quad_check_on`), soundness via
`geometry/SectionCapacity.ml` (`four_on_one_cut`).

C713 step 5 (`C713ChordDirect.source_to_after_height`): owner 2304 and the three squares
of masks 2, 512, 16384 containing the occupied-row points:
```
C713_HEIGHT : |- forall q n1 n2 n3. UNIT/SIDE/lcont for all /\ pairwise ldisj /\
                 (occupied-row point premises for n1 n2 n3, as in OccupiedRow.above_radius) /\
                 cov h713_d7_0 q ==> cov h713_d7_6 q
```

### 4.5 Case composition (worker ASSEMBLY)

Per case a **template theorem** in the shape accepted by `gen_case_thm_x`
(n12/geometry/gen_bridge.ml):
```
CK_TEMPLATE : |- forall sq_1 .. sq_m. <premises> ==> false
```
with premises among: `lsquare`, `lcont`, `ldisj` (needed pairs), side relations, `linside`
/ `lclosed` / `~linside` at rational points (the entry insideK/outsideK points and the
occupied-row points). Its proof is pure bookkeeping: instantiate `CK_INITIAL.(k)` for
each owner, chain `CK_STAGE.(NN)` (MP with its block-overlap theorem), `CK_CHORD.(NN)`,
height, in Lean's order (`Preservation/CK.lean` / `Cases/C713/Assembly.lean`), and close with
`oriented_pose_covered [] q <=> false`. Then `gen_case_thm_x` (extended for multi-set domains,
§4.3) yields `|- EXCLUDED_ROW ri`. Lean's `owner_disjoint` corresponds to the `ldisj`
premises (discharged by gen_bridge from `NPACK`).

### 4.6 C898 (W-C898; map §4)

Dictionary terms: `c8_row_tm`, `c8p_tm`, domains `c898_dA_B` (`c8dom_def "A_B"`), all in the CR_
representation (`CPose a rows`, a < 64, `s12_angles a = EL a angles64` = Lean's C898 angle).

- **Pair steps** (NN = 00..08, 11..14; implemented, `n12/cert/C8_Pairs.ml`):
  ```
  c8_step_thm "NN" : |- cr_block_overlap c898_sNN_hdrs (MAP cr_leaf c898_dN)
                        ==> cr_pair_transition (MAP cr_leaf c898_dS) (MAP cr_leaf c898_dN)
                                               (MAP cr_leaf c898_dT)
  ```
  (exactly §4.1). Plans + the 927 relaxation links are checked; the **open premise is the block
  overlap** (W-F345 interface, discharged as in §4.2, e.g. via `CR_BLOCK_OVERLAP_OF_PAIRS`).
  `c898_sNN_hdrs` lists one `(src, blk)` per plan: `NONE` (no obligation), `SOME rows`
  (Lean `blockRows k`, 500 blocks), and for step 14 `SOME []` for each of the 8 sources (Lean
  proves step 14 by one common point (10079/5000, 4914/5000) for all 8 × 53 pairs; the HOL step
  has no pieces, so the premise is the overlap of the whole source pose with every neighbour pose).
- **Initial covers** (W-F6 interface, §4.3 shape): `oriented_pose_covered (MAP cr_leaf c898_dK_0) q`
  for the 11 owners K ∈ {0,1,2,3,5,6,7,8,9,10,11} (Lean `C898Entry.ownerK_cover`, 704 recipes;
  owner 4 = mask 192 unused); W-ENTRY's C898 premises already exist (`en_run_case "898"`).
  **Done** (W-F6, `PV_C898.ml`): `pv898_initial_thm K` / `CK898_INITIAL`, §4.3 shape with
  `MAP cr_leaf c898_dK_0`.
- **Fused chord 9–10** (implemented, `C8_Fused.ml`): `C8_FUSED : |- c8_fused_transition
  (MAP cr_leaf c898_d5_0) (MAP cr_leaf c898_d0_9) (MAP cr_leaf c898_d7_7) (MAP cr_leaf c898_d11_0)
  (MAP cr_leaf c898_d3_3) (MAP cr_leaf c898_d6_5) (MAP cr_leaf c898_d9_8) (MAP cr_leaf c898_d5_11)`,
  where `c8_fused_transition S N1 N2 N3 M1 M2 M3 T` = for 7 squares q0..q6: UNIT and `&1 < a_i`
  for all, `lcont` for all, `ldisj` for the 12 pairs of the two windows ({0,1,2,3}, {0,4,5,6}),
  `a0 <= 1001/1000`, `lclosed q0 (33/20) (33/20)`, `lclosed q0 (47/20) (33/20)` (Lean
  PointPremises of owner 5), `cov S q0`, `cov N1 q1` … `cov M3 q6` ⟹ `cov T q0` (Lean
  `chord_fused`; q0 = owner 5, q1..q3 = owners 0, 7, 11, q4..q6 = owners 3, 6, 9).
- **Chain (W-ASM)**: steps 0–8, fused, 11–14 as in map §4; step 14 ends with `c898_d5_15 = []`.

---------------------------------------------------------------------------------------------

## 5. Reflective-checker technique (n12/cert/CR_Eval.ml, implemented)

1. Define the check as a HOL function `chk : data -> bool` by `define` with *executable*
   equations (pattern matching on constructors, `let` for shared sub-results — Compute is
   call-by-value, a non-`let` duplicate argument is evaluated twice).
2. Prove `|- chk d ==> semantic statement` once, by induction/rewriting (no evaluation).
3. Evaluate `chk d` for concrete `d` with `CR_EVAL_CONV`, an `hol-light/compute.ml`
   (`Compute.CBV_CONV`) compset containing the defining equations of all `cr_` checkers,
   list/option/pair/bool basics, constructor injectivity/distinctness
   (`injectivity "crow"` etc.), and externs for `int` arithmetic (`INT_ADD_CONV`,
   `INT_MUL_CONV`, `INT_SUB_CONV`, `INT_NEG_CONV`, `INT_LE_CONV`, `INT_LT_CONV`,
   `INT_EQ_CONV`, `INT_ABS_CONV`) and `num` comparisons (`NUM_LT_CONV`, ...).
   Data are literal terms (poses, rows); domain/header constants are never evaluated
   (they are connected to literals by their definitions and structural rules such as
   `cr_mem_rule`). `cr_prove_by_eval defs tm` optionally unfolds a few definitions first.
4. **Domains.** Compute compsets (and the term parser) are not Domain-safe: compsets are
   built in the **main domain** and handed to the workers (`cr_parallel_map nd f items`
   does this; `cr_cs ()` returns the current domain's compset). Never parse a quotation or
   print a term inside a worker. Terms/theorems may be shared across Domains read-only.
   To add checker equations: push to `cr_extra_thms` / `cr_extra_convs`, then
   `cr_cs_reset ()`.
5. Result theorems `|- chk d <=> true` are turned into `|- chk d` by `EQT_ELIM`, then
   `MATCH_MP` with the soundness theorem.

The same pattern is used by every later checker (F3–F6, chords, C898 links).

---------------------------------------------------------------------------------------------

## 6. Data extraction (n12/scripts/, n12/data/cert/)

`n12/scripts/cert_extract.py` (implemented; untrusted) reads the Lean sources and writes:

| file | format |
|---|---|
| `n12/data/cert/hist_rows.txt` | `id x y c strict denPred` (decoded raw rows, `B:` boxes, `M:`/`P:` strips and the inner tree nodes of `SharedRows.lean`) — 99,562 rows |
| `n12/data/cert/hist_poses.txt` | `id angle r1,r2,...` (pose lines + inner nodes of `SharedPoses.lean`) — 12,682 poses |
| `n12/data/cert/hist_domains.txt` | `case owner_version id1,id2,...` — 198 domains |
| `n12/data/cert/hist_stages.txt` | `case step srcDom nbrDom tgtDom nplans` — 113 pair stages |
| `n12/data/cert/hist_plans/C<case>_S<step>.txt` | one plan per line: `src B=r1,r2 tgt | hint;hint;...` (`B-` = no block, `B=` = `some []`, tgt `-` = empty plan); hint `d:<rh>` direct or `b:<rh>,<rh>,...` block; `<rh>` = `k` const, `c<i>` copy, `s<i>` single, `p<i>.<j>` pair |

Box/strip decoding follows `Core/BoxRowRecipe.lean` / `StripRowRecipe.lean` exactly (the
three `example`s of the Lean files are reproduced by the extractor). Later extractors
(fans, groups, initial batches, chords, C898) go to `n12/scripts/cert_extract_<topic>.py` and
`n12/data/cert/<topic>*.txt`, same style (one record per line, ids not literals).

---------------------------------------------------------------------------------------------

## 7. Files

| file | content |
|---|---|
| `n12/cert/CR_Row.ml` | §2 |
| `n12/cert/CR_Farkas.ml` | F1 (§3) |
| `n12/cert/CR_Plan.ml` | F2, plans, stages (§3, §4.1) |
| `n12/cert/CR_Eval.ml` | compset, `CR_EVAL_CONV`, parallel runner (§5) |
| `n12/cert/CR_HistData.ml` | dictionary/domain constants (§2.1) |
| `n12/cert/CR_HistStages.ml` | builds and checks all historical pair stages (§4.1) |
| `n12/cert/CR_HistRun.ml` | runs all 113 stages (`CK_STAGES`, `cr_hist_domains` = 12) |
| `n12/cert/cert_all.ml` | loads everything (needs p2_base + certlib) |
| `n12/cert/OV_Overlap.ml`, `OV_HistRun.ml`, `OV_Run.ml`, `CA_LoadOV.ml` | W-F345 block overlaps |
| `n12/cert/OV_C898.ml` | W-F345 for C898 (`ov8_step_thm`, needs C8_all) |

OCaml API for workers (all in the main domain unless noted):

| function | meaning |
|---|---|
| `cr_row_tm id`, `cr_rows_tm ids`, `hp_tm id` | historical row / row list / pose literal terms (memoized, shared) |
| `hist_rows_raw`, `hist_poses_raw`, `hist_domain_ids`, `hist_stages` | raw data tables |
| `hdom_def (case, "A_B")`, `hdom_const (case, "A_B")` | domain constant definition / constant |
| `cr_get_or_define name tm` | define a data constant (reload-safe) |
| `cr_plan_of_line`, `cr_stage_plans (case, step)` | plan terms from `n12/data/cert/hist_plans` |
| `ck_build_stage nd stage`, `ck_stage_thm (case, step)`, `ck_hdrs_tbl` | stage theorems (§4.1), header definitions |
| `CR_EVAL_CONV tm` | evaluation (any domain, after the compset exists for it) |
| `cr_prove_by_eval defs tm` | `|- tm` for a closed boolean evaluating to `T` |
| `cr_parallel_map nd f xs` | Domain pool with main-domain-built compsets |
| `cr_mem_rule x l` | `|- MEM x l` structurally for a literal list |

---------------------------------------------------------------------------------------------

## 8. Volumes and throughput

See map §3.7 and §9.

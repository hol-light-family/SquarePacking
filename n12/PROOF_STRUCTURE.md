# Structure of the proof of s(12) = 4

The proof is a port of the Lean 4 development by Jatloe, Gurevitch, Lewis and Ahmed
(`Queuingtheorydotcom/Jatloe12SquaresFormalized`, commit d0caf45).  The HOL files follow the
Lean modules, and most of them carry a comment `(* Lean: ... *)` naming the Lean theorem they
port.

```
SQUARE_PACKING_SIDE_12 : square_packing_side 12 = &4      PACKS_12 : forall t. packs 12 t <=> &4 <= t
      └──────────────┬─────────────────────────────────────────┘
          S12_SIDE_OF_NO_PACKING, PACKS_12_OF_NO_PACKING       (assembly.ml; with PACKS_12_4)
                     │
          S12_NO_PACKING : forall t. packs 12 t /\ t < &4 ==> false     (s12_no_packing)
                     ├─ S12_REDUCED_117   (Phase 1, phase1/): every packing with t < 4 gives a
                     │                    normalized packing NPACK whose marker family is one
                     │                    of 117 retained rows
                     └─ 117 × |- EXCLUDED_ROW ri   (Phase 2): no normalized packing has the
                                          marker family of row ri
PACKS_12_4 : packs 12 (&4)   (upper.ml: the 3 × 4 grid)
```

## Upper bound (`upper.ml`)

`PACKS_12_4`: twelve axis-parallel unit squares in a 3 × 4 grid inside [0,4]².  Their
interiors are disjoint by `DISJOINT_INTERIORS_SEPARATED` (`shared/squares_lib.ml`).

## Phase 1: reduction to 117 cases (`phase1/`)

Lean: `source/S12`, about 174 files, which use `native_decide` for the finite checks.  In HOL
every finite check is a kernel computation.

| step | HOL (file: theorem) | content |
|---|---|---|
| 0 | `normalize.ml`: `PACKS12_NORMALIZE` | a packing in side t < 4 rescales to 12 open squares of a common side a ∈ (1, 1.001] in [0,4]², pairwise disjoint; the squares are 5-tuples `c s u v a` (`linside`, `lcont`, `ldisj`) |
| 1 | `markers.ml`: `MARKER_NONAVOID`, `PACKS12_MARKER_OWNERS` | each square contains one of 16 fixed marker points |
| 2 | `groups.ml`: `OWNMASK_IN_TABLE` | the set of markers owned by one square is one of 103 groups |
| 3 | `families_check.ml`: `FAMILIES_CLASSIFIED`; `bridge.ml`: `VALIDF_OF_NPACK` | the 12 groups of a packing are disjoint; a kernel-checked search tree enumerates the possible families (in parallel, see `SQ_DOMAINS`) |
| 4 | `hull.ml`: `NOCONF_OF_NPACK`; `bridge.ml`, `auxcover.ml`: `FFP_BUDGET_F/G`; `singleton.ml` | 37 hull conflicts, the F/G pair budgets, singleton forcing |
| 5 | `transport.ml`: `PACKING_ROW` | D4 symmetry transport to a representative row; with steps 0–4 this gives `S12_REDUCED_577` (577 rows) |
| 6 | `localq.ml`, `step6.ml`, `step6_run.ml`: `PACKING_117`, `S12_REDUCED_117` | 1,721 local queries, 103 single and 25 combined domain specifications; 41 diagonal rows and 419 core proofs exclude 460 of the 577 rows |

The result:

```
S12_REDUCED_117 : forall t. packs 12 t /\ t < &4
                  ==> exists c1 c2 a b l r. NPACK c1 c2 a b l /\ MEM r RETAINED /\
                                            IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r
```

`EXCLUDED_ROW ri` (in `step6.ml`) says that no normalized packing `NPACK c1 c2 a b l` has
marker family `ROW_LIST ri`.

## Phase 2: the 117 cases

Lean: `Compact/`, about 5,160 files and 451k lines.  Each case is a geometric exclusion that
uses wall signs, angle ranges, cross points and owned markers.

| layer | files | content |
|---|---|---|
| geometry | `geometry/` (≈1,520 files) | The hand geometry of the Lean `Compact/` library (`Geometry/`, `Preservation/`, `Completion/`, `Bridge/`, `Cases/`).  `p2_base.ml` sets up the square vocabulary.  `PackingContext.ml` and `CP_CommonCases_OriginalOwners.ml` give the packing context (owners, domains `cdom`/`hdom`).  `RowIdentity.ml` turns per-case statements into `EXCLUDED_ROW`. |
| pose semantics | `certlib/` (31 files, see `certlib/README.md`) | Lean `source/S12` pose semantics: angle enclosures (192 angles), pose regions, overlap and coverage certificates.  The certificate cases are stated against these definitions. |
| certificates | `cert/` | Reflective checkers.  A certificate is a HOL term; a checker function defined in HOL is proved sound once, and is then evaluated on the term by kernel computation (`CR_EVAL_CONV`).  Layers: pair stages (`CR_*`), block overlaps (`OV_*`), initial covers (`PV_*`), chord and height stages (`CH_*`), entry domains (`EN_*`), C898 (`C8_*`), case assembly (`CA_*`).  Design: `docs/cert_design.md`. |
| case drivers | `cases/` | The theorems `\|- EXCLUDED_ROW ri`; see below. |

How the 117 rows are closed (from the build log):

| driver | rows | method |
|---|---|---|
| `cases/variant.ml` | 11 | FourSquareVariant: a ported template theorem, with all premises derived from the packing by the generic bridge `geometry/gen_bridge.ml` (forced owners from certified domains, seed and query points, hull points) |
| `cases/foursquare.ml` | 15 | FourSquare, same method |
| `cases/highright.ml` | 15 | HighRight, same method |
| `cases/cs2_all.ml` | 36 | FourSquareConvex, OppositeCentralWalls, MergedTopFurther, C849851, MergedLower, Endpoint684, C84 and others |
| `cases/c868.ml` | 1 | C868: finite ownership and hand geometry |
| `cases/cert_cases.ml` | 7 | C701, C713, C717, C973, C978, C979, C898: certificate cases (`cert/`) |
| `port_data/case_thms.txt` | 33 | Per-case closers in `geometry/`, e.g. `C981Compact.ml`, `CP_OtherCases_C1091_Completion.ml` |

That makes 118 theorems for 117 rows: one row is closed twice.  `assembly.ml` checks that each
theorem is exactly `EXCLUDED_ROW ri` for a retained row, and that all 117 retained rows are
covered.

## Build order and cost

`make.ml` (generated by `scripts/mk_final.py`) loads the parts in this order:
1. Phase 1 (`cases/cs_load.ml`, `phase1/step6_run.ml`);
2. the geometry files, in Lean dependency order;
3. `certlib/`;
4. the certificate layers;
5. the case drivers;
6. the 33 per-case closers;
7. the assembly;
8. `statement.ml`.

Cumulative CPU time at the end of each stage, from the build of 2026-11-13/14 (`docs/build_2026-11-14.txt`):

| stage | CPU s |
|---|---|
| Phase 1 chain + bridges | 2,644 |
| Phase 1 reduction (`S12_REDUCED_117`) | 14,493 |
| geometry (1,521 files) | 25,897 |
| certlib | 25,950 |
| certificate stages | 33,060 |
| block overlaps | 58,579 |
| initial covers | 84,384 |
| certificate cases | 84,403 |
| variant, foursquare, highright | 95,598 |
| cs2, c868 | 108,516 |
| assembly | 108,529 |

CPU time exceeds wall-clock time because some stages run on several domains.

## Representation

Squares are 5-tuples `c s u v a`: unit normal `(c, s)`, lower corner coordinates `u, v` in the
rotated frame, side `a`.  Lean's structure invariants become explicit hypotheses
`c * c + s * s = &1 /\ &0 < a`.  `docs/audit.md` compares a sample of 57 statements with their
Lean counterparts.  `docs/lean_comparison.md` compares the port with the Lean development and lists what the port
found about the Lean sources.

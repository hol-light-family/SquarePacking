# Independent audit of the HOL Light s(12) = 4 port (2026-11-13)

Question for a skeptical reader: does `|- square_packing_side 12 = &4` really follow, and are the
ported statements faithful to the Lean development (Jatloe et al., n12/ext/jatloe/Lean/Proofs/N12-jatloe)?

Short answer:
- **Soundness.** The final theorem is a HOL Light kernel theorem about standard Multivariate notions
  (isometric images of [0,1]^2, interiors, inf). No axiom, `mk_thm`, `CHEAT_TAC`, `Obj.magic`, user printer
  or interface overloading is used anywhere in the project. The HOL Light checkout is unmodified
  upstream (jrh13, e5236a5; `git status` shows no tracked changes). So the theorem is proved
  **once the definitive build shows it with no hypotheses**. When this audit was written the build
  `run/pipe_make_s12_final1.log` was still running (Phase-1 chain done after 2644 s, no exceptions so far),
  so that last confirmation is still pending (see §6).
- **Faithfulness.** I compared 34 case-closer/template theorems and 23 random geometry theorems with
  their Lean statements: no weakening and no added hypothesis. The documented deviations are
  harmless (§4).
- **Defect fixed.** One defect, in the build *reporting*: `n12/scripts/mk_final.py` printed
  "check_axioms passed" unconditionally, and never failed when hypotheses remained (§6). No proof file
  needed a change.

## 1. Top-level statement

**Definitions.** `shared/squares_defs.ml`:
- `unit_square S <=> exists f. (forall x y. dist(f x,f y) = dist(x,y)) /\ S = IMAGE f (interval[vec 0,vec 1])`.
  This is any congruent copy of the closed unit square; rotations, reflections and translations are
  all allowed.
- `packs n t <=> exists sq. (forall i. i < n ==> unit_square(sq i) /\ sq i SUBSET interval[vec 0,t % vec 1]) /\
  (forall i j. i < n /\ j < n /\ ~(i = j) ==> DISJOINT (interior(sq i)) (interior(sq j)))`.
- `square_packing_side n = inf {t | packs n t}`.

This is the squaremath.org problem: s(n) is the smallest side of a square that contains n unit squares
with pairwise disjoint interiors. Squares are indexed, so coincident squares are excluded. The definitions are
written independently of Lean. Lean's `S12.packingConstant12 = sInf {L | 0 < L /\ Nonempty (UnitPacking L)}`
(source/S12/PackingConstant.lean) uses open squares of side 1, `Inside -> [0,L]^2`, and pairwise
disjoint open squares. The two are equivalent: open square = interior of the closed square. The HOL
definition is the more standard one, and the HOL chain starts from it directly. Nothing is
transported from Lean's definition.

**Assembly** (`n12/assembly.ml`):
- `S12_SIDE_OF_NO_PACKING : (forall t. packs 12 t /\ t < &4 ==> false) ==> square_packing_side 12 = &4` is
  proved by REAL_INF_UNIQUE together with `PACKS_12_4` (the 4x3 grid, n12/upper.ml).
- `assemble_s12` accepts only theorems whose conclusion is `aconv` to `EXCLUDED_ROW ri` for a retained row.
  Any retained row not supplied becomes an explicit hypothesis `EXCLUDED_ROW ri`. The final theorem is
  therefore hypothesis-free exactly when all 117 rows are proved.

**Phase-1 chain:**
1. `PACKS12_NORMALIZE` (n12/phase1/normalize.ml): `packs 12 t /\ t < &4 ==> exists c1 c2 a b l. NPACK c1 c2 a b l`.
   It uses UNIT_SQUARE_NORMAL to write each square as `rsq c1 c2 a b` with a, b >= 0, then scales by
   k = min(4/t, 1001/1000). This gives:
   - a common side l in (1, 1001/1000];
   - closures inside [0,4]^2 (`owalls`, an exact bounding-box condition);
   - pairwise disjoint open squares (via `OSQ_SUBSET_INTERIOR_RSQ`).

   This is Lean's `UnitPacking.normalize`, and NPACK matches Lean's `NormalizedPacking` field by field.
2. `S12_REDUCED_117` (n12/phase1/step6_run.ml): `packs 12 t /\ t < &4 ==> exists c1 c2 a b l r. NPACK .. /\
   MEM r RETAINED /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list r`. It is built from
   PACKING_ROW (577 rows), 41 diagonal rows and the 419 core exclusions.
3. `EXCLUDED_ROW ri` (n12/phase1/step6.ml) is the term
   `~(exists c1 c2 a b l. NPACK c1 c2 a b l /\ IMAGE binarysum (FFP c1 c2 a b l) = set_of_list (ROW_LIST ri))`.
   It quantifies over **all** normalized packings, including the side l. It is the same term that
   the reduction produces, so the 117 exclusions close the chain.
4. Case theorems given in Lean's `excl_case id` form are converted by `ri_excluded_row`
   (p2/RowIdentity.ml). This is a kernel derivation, finished by `EQ_MP (ALPHA ..)` against
   `EXCLUDED_ROW i`. `excl_fam` / `excl_case` are faithful to `S12Completion.ExcludesFamily` /
   `ExcludesCase`, and the retained index list is proved equal to the expected-id filter
   (`RI_RETAINED_INDEX_EQ`).

**Verdict:** sound. Because the result is a kernel theorem, every intermediate statement (including
any mistranslated one) can only make the build fail. None of them can make the theorem false.
Faithfulness of intermediate statements matters for the claim "this is a port of Jatloe's proof",
not for the truth of the final theorem.

## 2. review.txt items

| item | verdict |
|---|---|
| c1091ri_input omits the unit-normal field | **Resolved, harmless.** The only theorem concluding it is `C1091RP_RESIDUAL_INPUT` (q = the owners). Lean's `Input` has the same 29 fields (checked one by one); the unit normals are inside Lean's OpenSquare. For owners they are `OO_UNIT` theorems, and the only consumer (`C1091RP_IMPOSSIBLE_OF_RESIDUAL_ENTRANCE`) supplies them with `ASM_SIMP_TAC[OO_UNIT]`. In the packing context nothing is lost. C1091 is closed by `CP_OtherCases_C1091_Completion.ml` independently of this route. |
| C1092WallCycle.ml generated from templates/C1092WallCycle.tpl | **Consistent.** Expanding the template with run/ctxw/expand.py, plus the two macros `OWNW(k)` and `WF(k)` that the copy of expand.py lacks, reproduces C1092WallCycle.ml byte for byte. Note: run/ctxw/expand.py is stale (it lacks OWNW/WF). Regenerating with it would give an unparsable file, not a wrong one. |
| OO_CHAIN_TAC 'seqapply: Length mismatch' | **Completeness bug only** (a tactic fails, so no theorem is produced). It has no soundness impact; the workaround is in use. Left unfixed. |
| Prefix07/08 load-tested via renamed copies | **Confirmed.** The fresh single-process build `run/pipe_make_s12.log` (started 2026-11-12 23:01, after the files' last change at 19:49/19:50) defines C981CP07_STEP07 / C981CP08_STEP08. The whole log contains no exception. |
| 4 C1092 files loaded in pieces | **Confirmed** in the same fresh build: CrosspointBoundaryG01, MissingNegativeCrosspointG01Models, MissingNegativeCrosspointG11 and OnePositiveScalars all define their last theorem, with no exception. The files are unchanged since 19:15-19:26. |
| C705716_InitialDomains loaded in two parts | **Confirmed** in the same fresh build (C705716ID_INITIAL_NAMED_T; the file is unchanged since 22:10). |
| C983_F4MergedCenter reloaded mid-file; TopOriginSign claim | Fresh load **pending**: the file changed at 00:39 Nov 13, after the old build started; to be confirmed by final1. TopOriginSign is resolved (BranchEnding 1 proved outright, C1092MTFE_BRANCH_ENDING; C1092CC_EXCLUDED_ROW closes all four branches). |
| UNPORTED trig lemmas (F4MergedCenterMonotone, F4BarAngleScalars) | **Confirmed unused.** In Lean, F4MergedCenterMonotone is imported only by F4MergedCenterEnding (uses `positive_comparisons`), F4BarAngleScalars (uses `canonical_angle` only inside the *proof* of `vertex_gap`) and F4MergedCenterPositive. HOL ports `positive_comparisons` (C983FMCM_POSITIVE_COMPARISONS) and `slope`/`vertex_gap`/`half` with trig-free proofs. Unported names have no HOL constants, so no HOL theorem can depend on them. |
| C1089 SingletonCorner corner_of_seeds uses `apart` in both orders | **Resolved.** The HOL hypotheses are the specific ordered `ldisj` instances that are used. Each is an instance of Lean's universally quantified `apart`, so the HOL statement is at least as strong. All consumers (C1089SC_ORIGINAL_CORNER_OF_SEEDS, C1091ER_*, C1089LSRP_SINGLETON_CORNER) are `prove` results, so they discharged every instance (e.g. (12,8192) and (8192,12) via `c1089sc_apart`). |
| CP_OtherCases_C983_F4Completion re-run mid-file | Fresh load **pending** (file changed 05:32 Nov 13); to be confirmed by final1. |
| AFTER all proofs: check_axioms; cosmetic `forall`/`exists` pass | `check_axioms` is in the build, but its "passed" message was unconditional (fixed in the generator, §6). The cosmetic syntax pass is **not done yet**: 1081 p2 files still use `forall x.`. It is cosmetic and scheduled after the final build. |

## 3. OCaml-gated producers and forbidden constructs

**Grep** over src/, run/cases/ and make_s12_final1.ml:
- No hits for `mk_thm`, `new_axiom`, `CHEAT_TAC`, `Obj.`, `Marshal`, `new_basic_type_definition`,
  `new_specification`, `new_type`, `new_constant`, `install_user_printer`, `overload_interface` or
  `override_interface`.
- No top-level rebinding of kernel or core names (`prove`, `concl`, `hyp`, `axioms`,
  `check_axioms`, ...).
- One `new_basic_definition` (n12/cert/CR_HistData.ml:83, `cr_get_or_define`). It defines a constant
  as a closed list term, which is conservative. On reload it re-uses the existing definition only if it is
  `aconv` equal, and fails otherwise.
- Top-level `ASSUME`s (about 15 files, e.g. CP_CommonCases_C1084.ml, C1072, C893, C982, C997,
  SideSignPacking) are packing-context hypotheses that the same file discharges by DISCH, CHOOSE or
  NOT_INTRO. HOL's `prove` rejects results with extra assumptions (tactics.ml:902), and any leftover
  hypothesis would be visible in the final theorem.

**Producers reviewed** (about 20; details in the audit transcript):
- Caches: cdom_cache/hdom_cache, dc_cache, LQ_TABLE/pk_lq, the SLQ tables (slq_select/new/hist),
  PK_COMB_TBL/SPEC_TBL, SETLIT_TBL, OO_SEED_TBL.
- oo_seed/oo_known/oo_missing, pk_forced, pk_domain_cases, pk_product/pk_remove, dt_trim and
  dt_refine_against, oo_four_point.
- pp_sound (checks `concl th = goal`), tob_transformed_singleton, tod_transported,
  dht_check_points (Lean quarterFG_points), mq_single/mq_extended, umd_domain33792,
  c1090ac_transported_cover (swapGF_points etc.).
- c981or_excludes_with, c981we_check/excludes, C981CF_TR_TBL, wsfs_original_bottom, the ri_* functions,
  and ca_premise/CA_COVERS.

Every one returns a kernel theorem built by `prove` or inference rules. In every case the OCaml
boolean checks only decide whether a proof is attempted or which data or hints are used: transformed
queries are re-proved at the image points, and cached entries are used through MP/MATCH_MP against
the caller's own hypotheses. A wrong cache entry can only make a later step fail. No producer catches a
failure and substitutes an ASSUMEd or weaker theorem. The one deliberate exception is
`ca_premise`, which returns `ASSUME t` for an unprovided certificate premise. The final script keeps only
CA_EXCLUDED theorems with `hyp = []`, and any rows dropped that way would surface as final hypotheses.
Minor: `wsfs_original_bottom` builds its intended conclusion and then ignores it (no shape check). This is not a
soundness issue.

## 4. Faithfulness spot-check

**Case closers and templates (34 theorems, about 25 cases).** Checked:
- the templates FSLB_IMPOSSIBLE, FSHR_IMPOSSIBLE, CWC_POINT and C84MP_IMPOSSIBLE;
- the case and family theorems of C997, C982, C893, C1084, C48 rows, CentralPair, C888/889,
  C896, C975, C983 (C974LocalEnding, F4Completion, ThreeBranches), C974, C1090, C715, C705/716,
  C868, C1092 (excludes_case, pending_closed), C981 (Obligations, 8 fields), C977, C696, C580/581,
  C1089, C1091, C972, C976 and C700.

All are faithful; where they differ, the HOL statement is stronger (e.g. `&0 < a` dropped because
`&1 < a` is present). Template drivers (gen_case_thm_x, case_ctx/apply_tmpl/close_case, fs_case_thm)
instantiate `prove`d templates, and every premise is discharged from NPACK_SQ, NPACK_LDISJ, OWALLS_LCONT,
domain theorems and seeds. MTF_IMPOSSIBLE / C849851_IMPOSSIBLE (p2/hand_wrappers.ml) are documented
restatements with no single Lean counterpart; their EXCLUDED_ROW results are what count.

**Random geometry theorems (23 from 15 files, fixed-seed shuffle).** Files: CentralSegmentAngle,
CP_CommonCases_InwardPoint, DiagonalWallCenter, CP_FiniteCases_WallHighFromMarker,
CentralNegativeSignedPositiveBottom, LongSection, CentralWallPairSupport, RightWallOuterSegment,
CP_OtherCases_CrossedElbow, CornerWallMarkerNegativeHighBounds, DiagonalOuterPoint,
FullAuxWallOppositeAxes, PositiveBottomSupport, CP_FiniteCases_MergedCornerPoint and
UpperRightCornerLongitudinalBounds.

All are faithful. Rational constants, strict versus non-strict inequalities, Inside versus ClosedInside,
signs (`-q.s`), the `ldisj` order, and existential squares (which carry their unit normal and `0 < a'`) all match.

**Documented representation differences** (all harmless):
- Explicit unit-normal and positive-side hypotheses.
- `c1091ri_input` without unit normals (§2).
- Specific `ldisj` instances instead of a universal `apart`.
- Proof-only replacements: trig/derivative arguments replaced by half-angle algebra or Bernstein/NLIN
  certificates, and triangle certificates replaced by the convex combinations they certify. These do not
  change any statement.

**Findings about the Lean side** are collected in n12/docs/port_findings.md: many files headed "Source only,
uncompiled", all re-proved as stated in HOL.

## 5. Unported Lean items

- Every non-certificate, non-template module in the import closure of `Compact.Assembly.Final` has a
  p2 file. I checked this with n12/scripts/ready.py's closure and the same name mapping: 0 modules missing.
  The certificate/template modules (Compact.Cases, Historical*, Core, Preservation, Assembly) are
  re-implemented by n12/cert, n12/certlib, n12/cases and the Phase-1 layers.
- The "not yet ported" rows in the first table of n12/docs/port_findings.md are **stale**. Every file listed
  there (C896Completion, C1089/AuxiliaryCover, ContinuousBottom, LastSectorExtra, OriginalEnding,
  SingletonCorner, WallOrigins, C1090/AuxiliaryCover, EarlySelection, ResidualOwners, C976LeftTop/Main,
  MergedPending/C700Completion and Completion, OrdinaryCentralReduction, ShallowTopPair, and
  MPPMOrdinaryWallAdvance) now has its HOL port. So do the later "returned unported" items: C981WallElbows,
  DiagonalAuxiliary, OwnerTransport, MPPMCrosspointBoundaryG01/G11, MissingNegativeCentersSupport and
  NegativeMissingPositiveSharedWall. Compact/Assembly/Endpoint684 is assembly-level; its case is handled
  by the template drivers.
- The only remaining unported statements are the trigonometric lemmas of C983 F4MergedCenterMonotone /
  F4BarAngleScalars (canonical_angle, Bminus, Bplus, G, their monotonicity lemmas, and J/derivative).
  They are unused (§2).
- Conditional Lean results ported as conditionals (e.g. ProfileAdapter `derive`, ActualProfile
  WallPoints, NegativeCrosspointActual ScalarProof, C977/C1090 entrance contracts) are not on the path
  to the final theorem. The case closers in n12/port_data/case_thms.txt are hypothesis-free `EXCLUDED_ROW` /
  `excl_case` theorems, and `fin_excluded` rejects any with hypotheses.
- Structurally, an unported item cannot be used: it has no HOL constant or theorem. The only way it
  could enter is as an assumption, and that would show up as a hypothesis of the final theorem.

## 6. Build reporting defect (fixed) and what to check in the final log

The final build is piped into the toplevel (shared/build.sh), where an exception aborts only the
current phrase. The generated make_s12_final1.ml ends with:
```
Printf.printf "FINAL hypotheses remaining: %d\n%!" (length (hyp S12_SIDE));;
S12_SIDE;;
axioms();;
check_axioms ();;
print_string "FINAL check_axioms passed: only INFINITY_AX, SELECT_AX, ETA_AX\n";;
```
So "check_axioms passed" is printed even if `check_axioms` raised, and a non-zero hypothesis count is only
printed. Fix in `n12/scripts/mk_final.py` (the generator; I did not touch the running build's file): each
check is now a single phrase. One prints `FINAL RESULT CHECK passed/FAILED` (hyp = [] and concl =
`square_packing_side 12 = &4`), and the other prints `FINAL check_axioms passed/FAILED`. The generated
output is otherwise identical to make_s12_final1.ml.

**For the current run (make_s12_final1)**, accept the result only if the log shows all of the following:
- `assemble_s12: 117 of 117 retained rows proved, 0 assumed`;
- `FINAL hypotheses remaining: 0`;
- `val S12_SIDE : thm = |- square_packing_side 12 = &4`;
- `axioms()` listing only INFINITY_AX, SELECT_AX and ETA_AX;
- **no `Exception` line directly after `check_axioms ();;`**.

Also check that there are no `STAGEFAIL` lines, in particular none for
CP_OtherCases_C983_F4MergedCenter / F4Completion, the two review items still pending.

## 7. Open concerns

1. The definitive build has not finished. Its result must be read as described in §6.
2. Fresh-build confirmation of CP_OtherCases_C983_F4MergedCenter.ml and F4Completion.ml is pending
   (final1). An own `audit` server was started for this but stopped before cs_load finished: the
   ~200-270-file dependency chain would duplicate what final1 is doing anyway.
3. Robustness, not soundness:
   - variant.ml skips `check_case_thm`;
   - `fin_add` does not check `hyp` for the driver lists (the final hypothesis count covers it);
   - run/ctxw/expand.py is stale;
   - OO_CHAIN_TAC has a single-step bug;
   - README.md still says "s(12) = 4 is not proved here";
   - the "not yet ported" table in n12/docs/port_findings.md is stale.
4. OCaml 5 domains are used for parallel checking (families_check, cert). Data races in OCaml 5 are
   memory-safe and theorems remain abstract values, so this cannot forge theorems. The only shared mutable kernel state is the
   constant/definition tables, and those are written only from the main domain (n12/docs/cert_design.md §5.4).

## Addendum (2026-11-14)

The open points of this audit have since been settled:

- **Definitive build.**  It finished at 02:19 UTC on 2026-11-14.  The log shows:
  - `assemble_s12: 117 of 117 retained rows proved, 0 assumed`;
  - `FINAL hypotheses remaining: 0`;
  - `val S12_SIDE : thm = |- square_packing_side 12 = &4`;
  - `axioms()` listing only INFINITY_AX, SELECT_AX and ETA_AX, and no exception after
    `check_axioms ()`;
  - no `STAGEFAIL` line (so CP_OtherCases_C983_F4MergedCenter and F4Completion loaded fresh).

  See `build_2026-11-14.txt`.  The build ran on HOL Light commit e5236a5.  The current commit,
  b5d59ef, differs from it only in version metadata (`META`, `hol.ml`, `opam`).
- **Syntax pass done.**  All sources now use `forall`/`exists`/`existsunique`/`true`/`false`.
  The pass was token-based and was checked quotation by quotation.
- **README updated.**
- **Findings documents.**  The working documents referred to above (`review.txt`, the review
  queue, and `port_findings.md`, the porting log with its stale "not yet ported" table) have been
  replaced by `lean_comparison.md`.  Their resolved items are recorded in §2 and §5 of this audit.
- **File paths changed.**  The tree was reorganized after the audit:
  - `src/port/p2` is now `n12/geometry`;
  - `src/port/p3` is now `n12/certlib`;
  - `src/port/{cert,cases}` are now `n12/{cert,cases}`;
  - the other `src/port` files are in `n12/phase1`;
  - `make_s12_final1.ml` corresponds to `n12/make.ml`;
  - `run/` logs are no longer part of the repository.
- **Additional theorem.**  `n12/assembly.ml` now also exports
  `PACKS_12 : forall t. packs 12 t <=> &4 <= t`.  It is derived from the same no-packing theorem
  as `square_packing_side 12 = &4`, with `PACKS_12_4` and `PACKS_MONO`.


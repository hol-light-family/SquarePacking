# shared/

This folder holds what every case `n<N>/` has in common: the definitions that the statements
depend on, general lemmas, the proof tools and the build script.  Paths are relative to the
project root, and every build runs from there.

## Definitions and lemmas

| file | content |
|---|---|
| `squares_defs.ml` | **The definitions used in every statement**: `unit_square`, `packs`, `square_packing_side`.  It loads only HOL Light's `Multivariate/convex.ml`.  This is the only project file that a case's `statement.ml` depends on, and it should not change. |
| `squares_lib.ml` | General lemmas about unit squares and packings (loads `squares_defs.ml`). <br>`UNIT_SQUARE_BOX`: a unit square is a box `sqbox p u w` with corner `p` over an orthonormal frame `u, w`. <br>`IN_INTERIOR_SQBOX`: points strictly inside the box are in its interior. <br>`DISJOINT_INTERIORS_SEPARATED`: two sets separated by a line have disjoint interiors. <br>`PACKS_MONO`: `packs n t /\ t <= t' ==> packs n t'`. <br>`PIGEONHOLE_POINTS`: n points taken from fewer than n values cannot all be distinct. |

## Proof tools (`tools/`)

Each tool pairs an untrusted search with a kernel-checked proof.  The search, in OCaml or in a
Python oracle, only proposes a certificate; HOL Light proves the goal from it.  A wrong
certificate can only make the tactic fail.

| file | content |
|---|---|
| `tools/nlin.ml` | `NLIN_TAC`, an `nlinarith`-style prover for real polynomial inequalities.  Pairwise products of the hypotheses are formed; the LP oracle `tools/nlin_lp.py` picks a subset with a linear contradiction; `REAL_ARITH` proves the contradiction from that subset.  Variants: `DISJ_NLIN_TAC`, `NLIN_FACTS_TAC`. |
| `tools/nlin_lp.py` | The untrusted LP oracle for `NLIN_TAC`.  It solves an LP with SciPy and reports which facts the linear certificate uses.  It runs as a subprocess server. |
| `tools/bernstein.ml` | `ARC_NONNEG`: proves that a polynomial in `(c, s)` is nonnegative on the quarter unit arc.  It uses the rational parametrisation `c = 2t/(1+t^2)`, `s = (1-t^2)/(1+t^2)` and Bernstein subdivision.  This gives bounds over all orientations of a square without trigonometry.  Loads `tools/nlin.ml`. |
| `tools/cover_tac.ml` | `COVER_TAC`: proves that a polygon of square centres is covered by triangle lemmas.  It replays a case tree with case splits and `REAL_ARITH`.  Loads `tools/nlin.ml`. |
| `tools/cover_search.py` | The untrusted search that finds the case tree for `COVER_TAC`.  `COVER_TAC` passes it the problem and reads back the tree through temporary files (`Filename.temp_file`, in `$TMPDIR` or `/tmp`), which it then deletes. |
| `tools/domains.ml` | `sq_ndomains n`: the number of OCaml domains a parallel proof step that asks for n domains gets, i.e. `min n cap`.  The cap is the environment variable `SQ_DOMAINS` if set, else `Domain.recommended_domain_count ()`; the log prints it as `parallel steps use at most cap domains`.  The kernel is purely functional, so parallelism changes only the speed.  Needs OCaml 5. |

The Python oracles are run with `$SQ_PYTHON` if set, else `.venv/bin/python` under the project
root if it exists, else `python3`.  Both need SciPy.

## Build script

`build.sh` builds one case in a fresh HOL Light session:

```
HOLLIGHT_DIR=/path/to/hol-light shared/build.sh n<N>/make.ml
```

- It pipes the make file into HOL Light's launcher `$HOLLIGHT_DIR/hol.sh`.
- An error in one phrase does not stop the rest of the build, and shows up in the log.
- The log is written next to the make file (`n<N>/make.log`), and the summary lines are printed
  at the end.
- There is no time limit.  Wrap the call in `timeout` if you want one.
- Exit status: 0 if the log contains a `STATEMENT CHECKED` line, printed only after the
  mechanical check of the statement has passed, and no error line (`Error`, `Exception`,
  `FAILED`, `STAGEFAIL`); 1 otherwise.

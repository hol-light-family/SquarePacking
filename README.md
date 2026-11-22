# Packing unit squares in a square, in HOL Light

This repository formalizes cases of the [Squares Project](https://squaremath.org/) in
[HOL Light](https://github.com/jrh13/hol-light).  The project asks for *s(n)*, the side of the
smallest square that contains *n* non-overlapping unit squares.  Each solved case lives in its own
directory `n<N>/`.  Everything the cases have in common (the definitions and the proof tools) is
in `shared/`.

## The statement

The definitions are in `shared/squares_defs.ml` and use only HOL Light's standard notions:

```
unit_square (S:real^2->bool) <=>
    exists f:real^2->real^2. (forall x y. dist(f x,f y) = dist(x,y)) /\
                             S = IMAGE f (interval[vec 0,vec 1])
packs (n:num) (t:real) <=>
    exists sq:num->real^2->bool.
        (forall i. i < n ==> unit_square(sq i) /\ sq i SUBSET interval[vec 0,t % vec 1]) /\
        (forall i j. i < n /\ j < n /\ ~(i = j) ==> DISJOINT (interior(sq i)) (interior(sq j)))
square_packing_side n = inf {t | packs n t}          (a real number)
```

`real^2` is the Euclidean plane, `interval[vec 0,vec 1]` is the closed square [0,1]² and
`interval[vec 0,t % vec 1]` is [0,t]².  Each `n<N>/statement.ml` explains these constants and
gives the file and line of their definitions in HOL Light.

A unit square is any congruent copy of [0,1]², so rotations, reflections and translations are
all allowed.  The squares must lie in [0,t]², and their interiors must be pairwise disjoint;
boundaries may touch.  The result for a case `N` with value `v` is a pair of theorems, both
with no hypotheses:

```
SQUARE_PACKING_SIDE_<N> : |- square_packing_side N = v
PACKS_<N>               : |- forall t. packs N t <=> v <= t
```

`PACKS_<N>` is the stronger of the two.  It also says that the infimum is attained, i.e. there is
a packing in a square of side exactly `v`.  `SQUARE_PACKING_SIDE_<N>` follows from it, and both
are stated so that the reader does not have to derive one from the other.

HOL Light has no database of named theorems: `SQUARE_PACKING_SIDE_<N>` and `PACKS_<N>` are the
names of OCaml values of type `thm`, bound in the HOL Light session by `n<N>/make.ml`.

## Layout

```
shared/squares_defs.ml    the definitions above (the only file a statement depends on)
shared/squares_lib.ml     common lemmas: unit squares as boxes over orthonormal frames,
                          interiors, separation, monotonicity of packs
shared/tools/             proof tools, each with an untrusted search and a kernel check:
                          nlin.ml (+ nlin_lp.py), bernstein.ml, cover_tac.ml (+ cover_search.py),
                          domains.ml (the SQ_DOMAINS cap on parallel steps)
shared/build.sh           builds one case in a fresh HOL Light session (via hol.sh)
shared/README.md          what is in shared/
n<N>/README.md            the case: result, files, build instructions, build time and memory
n<N>/PROOF_STRUCTURE.md   the structure of the proof
n<N>/statement.ml         the theorems, for auditors (see below)
n<N>/make.ml              loads the whole proof, then statement.ml
```

**Auditors: read `n<N>/statement.ml` first.**  It states the two theorems as HOL terms and
explains, in comments, every constant they use, with the file and line of its definition.  At
the end of `make.ml` it also checks mechanically three things:
- the proved theorems have exactly those conclusions (up to renaming of bound variables);
- they have no hypotheses;
- `check_axioms ()` passes, i.e. only HOL Light's three standard axioms (`INFINITY_AX`,
  `SELECT_AX`, `ETA_AX`) are used.

The expected terms are parsed when `statement.ml` is loaded, that is, after the whole proof has
been loaded into the same session.  How a quotation parses depends on the session's parser
settings (overloading, infix operators, type priorities).  No file in this repository changes
them: there is no `overload_interface`, `override_interface`, `reduce_interface`,
`make_overloadable`, `parse_as_infix`, `parse_as_prefix`, `parse_as_binder` or `prioritize_*`
call, and the HOL Light library files that the proofs load (`Multivariate/convex.ml`, through
`shared/squares_defs.ml`, and `Library/binary.ml`) do not change them either.  The
expected terms are therefore parsed as in a fresh session that has loaded only
`shared/squares_defs.ml`.  (Checked with `grep`; please repeat the check for a new case.)

## Building

You need:
- **OCaml 5.**  The builds were checked with OCaml 5.5.2, the version that HOL Light's
  `make switch-5` installs (with camlp5 and zarith).  Proof steps that run on several OCaml 5
  domains (see below) cannot be built with OCaml 4.
- **HOL Light**, a git checkout of [jrh13/hol-light](https://github.com/jrh13/hol-light) built
  with `make` in its directory, which creates `hol.sh`.  The HOL Light commit each case was
  checked with is given in its `n<N>/README.md`.  Building with `make` (the default,
  `HOLLIGHT_USE_MODULE=0`) or with `HOLLIGHT_USE_MODULE=1 make` should not change the result;
  each case's README says which one its recorded build used.  A HOL Light installed with
  `opam install hol_light` has not been tried.
- **Python 3 with SciPy**, for the cases whose proofs call the Python oracles of
  `shared/tools/` (each case's README says whether it does).  Either set `SQ_PYTHON`, or create
  `.venv` in the project root (`python3 -m venv .venv && .venv/bin/pip install scipy`).

Then, from the project root:

```
HOLLIGHT_DIR=/path/to/hol-light shared/build.sh n<N>/make.ml
```

The log is written next to the make file (`n<N>/make.log`).  It contains a line
`n=<N> STATEMENT CHECKED: ...` when everything succeeded.  `build.sh` exits with status 0 if
the log has that line and no error line (`Error`, `Exception`, `FAILED`, `STAGEFAIL`), and
with status 1 otherwise.  An error in one phrase does not stop the build, so a failed build
still runs to the end.  There is no time limit; each case's README gives the time and memory
it took.

Some proof steps run on several OCaml domains (cores).  Each such step asks for a fixed
number of domains, which is capped by `SQ_DOMAINS` if it is set, and otherwise by
`Domain.recommended_domain_count ()` (normally the number of cores).  The log prints the cap
as `parallel steps use at most k domains`.  Parallelism changes only the speed, not the
theorems proved.

## Adding a case

To contribute a new case `n<N>/`:

1. Load `shared/squares_lib.ml`, which loads `shared/squares_defs.ml`, and do not change the
   shared definitions.
2. Write `n<N>/statement.ml` in the style of the existing ones.  It should contain:
   - the expected terms of the two theorems above, bound as `SQUARE_PACKING_SIDE_<N>_STATEMENT`
     and `PACKS_<N>_STATEMENT`;
   - comments on the constants they use;
   - the mechanical check, which compares each theorem `NAME` (bound by `make.ml`) with
     `NAME_STATEMENT`.
3. Write `n<N>/make.ml` so that it ends with `loadt "n<N>/statement.ml";;`.
4. Write `n<N>/README.md` (the result, the files, how to build, and the build time, memory
   and versions used) and `n<N>/PROOF_STRUCTURE.md` (the structure of the proof).

Paths inside HOL files are relative to the project root.  Temporary files go to the system
temporary directory (`Filename.temp_file`, i.e. `$TMPDIR` or `/tmp`).  Keep large or
regenerable data out of git (see `.gitignore`).

## Trust

The trusted base is the HOL Light kernel and its three standard axioms.  No `new_axiom`,
`mk_thm` or `CHEAT_TAC` is used.  OCaml and Python programs only search for proofs or
certificates; whatever they find is re-checked by the kernel, so a wrong search result can only
make a proof fail.  HOL Light built with `HOLLIGHT_USE_MODULE=1` also trusts its file inliner
`inline_loads.ml` (see HOL Light's README); the default build does not.

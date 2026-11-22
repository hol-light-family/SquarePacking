# n = 5:  s(5) = 2 + √2/2

```
SQUARE_PACKING_SIDE_5 : |- square_packing_side 5 = &2 + sqrt(&2) / &2
PACKS_5               : |- forall t. packs 5 t <=> &2 + sqrt(&2) / &2 <= t
```

| file | content |
|---|---|
| `statement.ml` | the two theorems, every constant they use with its definition site, and the mechanical check |
| `PROOF_STRUCTURE.md` | the structure of the proof |
| `square5.ml` | the proof |
| `make.ml` | the build: loads `square5.ml`, then `statement.ml` |

The lower bound uses the "unavoidable points" of Göbel (1979) and Friedman; the upper bound is
Göbel's packing.

## Build

From the project root:

```
HOLLIGHT_DIR=/path/to/hol-light shared/build.sh n5/make.ml
```

The log `n5/make.log` ends with:

```
n=5 STATEMENT CHECKED: |- square_packing_side 5 = &2 + sqrt(&2) / &2 (no hypotheses; axioms: INFINITY_AX, SELECT_AX, ETA_AX only)
```

## Build environment

The build was checked on 2026-11-24 with:

| | |
|---|---|
| HOL Light | [jrh13/hol-light](https://github.com/jrh13/hol-light) master, commit `096417cac706ff0818f739bbc19f2ed499e43283` (2026-11-24), built with `HOLLIGHT_USE_MODULE=1 make` |
| OCaml | 5.5.2, camlp5 8.05.03, zarith 1.14 |
| machine | 96-core Arm Neoverse-V2, 185 GB RAM, Linux 7.0 |
| wall-clock time | 7 min 15 s (most of it loading HOL Light and its Multivariate library) |
| peak memory | 2.0 GB (maximum resident set size) |

Python is not needed for n = 5.

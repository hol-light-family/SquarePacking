# Structure of the proof of s(5) = 2 + √2/2

The whole proof is in `square5.ml` (about 440 lines).  It loads `shared/squares_lib.ml` and uses
from it:
- the representation of a unit square as a box `sqbox p u w` with corner `p` and orthonormal
  frame `u, w` (`UNIT_SQUARE_BOX`);
- the interior criterion `IN_INTERIOR_SQBOX`;
- line separation `DISJOINT_INTERIORS_SEPARATED`;
- monotonicity `PACKS_MONO`;
- `PIGEONHOLE_POINTS`.

Write r = √2 and v = 2 + r/2.

```
SQUARE_PACKING_SIDE_5 : square_packing_side 5 = v
  └─ PACKS_5 : forall t. packs 5 t <=> v <= t
       ├─ LOWER5        : packs 5 t ==> v <= t                  (lower bound)
       │    └─ NO_PACK5 : 0 < e <= 1/100 ==> ~packs 5 (v - e)
       │         ├─ KEY5   : every unit square in [0, v-e]^2 has one of the four points
       │         │           (a,a), (a,b), (b,a), (b,b) in its interior,
       │         │           a = 1 - e/4,  b = 1 + r/2 - 3e/4
       │         │    └─ KEY5U ─ CORE ─ CORE0 / CORE_LIN ─ BASIC5 ─ C_LEMMA
       │         └─ pigeonhole: 5 squares, 4 points, disjoint interiors  (CARD_LE_4)
       └─ GOEBEL_PACKS  : packs 5 v                              (upper bound)
            ├─ goebel_sq   : the five squares (four axis-parallel corner squares,
            │                one square at 45 degrees in the centre)
            ├─ GOEBEL_MEM  : each lies in [0,v]^2 (coordinate bounds)
            └─ GOEBEL_DISJOINT : interiors pairwise disjoint (a separating line per pair)
```

## Lower bound

1. **Elementary real lemmas** (`C_LEMMA`, `BASIC5`, `CORE_LIN`, `CORE0`, `CORE`).  Inequalities
   in r (with r² = 2), the gap e and the direction (u1, u2) of the square, with u1² + u2² = 1.
   They say that one of the candidate offsets (X, Y) lies within distance 1/2 of the
   square's centre in both frame coordinates.  These are polynomial inequalities over
   the unit circle, proved by case splits and real arithmetic.
2. **Key lemma** (`KEY5U`, `KEY5`).  `KEY5U` states the four-point property for a square given
   by its centre (c1, c2) and direction u.  `KEY5` restates it for the box form `sqbox p u w`
   used by `packs`.
3. **No packing just below v** (`NO_PACK5`).  Take five squares in [0, v−e]².
   - By `KEY5`, each contains one of the four points in its interior.
   - Two squares then share a point (`PIGEONHOLE_POINTS`, `CARD_LE_4`).
   - So their interiors meet, which contradicts disjointness.
4. **All smaller sides** (`LOWER5`).  If packs 5 t with t < v, then by `PACKS_MONO` also
   packs 5 (v − e) for some 0 < e ≤ 1/100, which `NO_PACK5` rules out.

## Upper bound

`goebel_sq r i` defines Göbel's packing:
- squares 0–3 are axis-parallel unit squares in the four corners of [0, v]²;
- square 4 is centred at (v/2, v/2) and rotated by 45°.

`GOEBEL_MEM` bounds the coordinates of every point of each square, so each square lies in
[0, v]².  `GOEBEL_DISJOINT` separates each pair of squares by a line.

## Main theorems

`PACKS_5` combines `LOWER5` with `GOEBEL_PACKS` and `PACKS_MONO`.  `SQUARE_PACKING_SIDE_5`
follows from it, because the infimum of {t | v ≤ t} is v.

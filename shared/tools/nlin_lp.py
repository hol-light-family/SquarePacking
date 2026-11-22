#!/usr/bin/env python3
"""Untrusted LP oracle for NLIN_TAC.

Input file: first line "n m nstrict-flags...": we use a simple format
  line 1: N K            (N candidate facts, K monomials)
  line 2: kinds          N tokens: 'ge' (p>=0), 'gt' (p>0), 'eq' (p=0)
  then N lines: sparse polynomial: count, then pairs  monomial_index  coeff(num/den)
Monomial index 0 is the constant monomial.
Output: indices of the facts used (support of a Positivstellensatz-style linear
certificate  sum l_i p_i = c  with  c <= 0, and c < 0 or some strict l_i > 0),
or "FAIL".
"""
import sys
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def exact_cert1(P, kinds, k, x, cols, thr, den):
    # combine pos/neg columns into one coefficient per fact
    lam = {}
    for v, (i, sg) in enumerate(cols):
        if x[v] > thr:
            lam[i] = lam.get(i, 0.0) + sg * x[v]
    S = sorted(lam)
    # equations: sum_i lam_i P_i[m] = 0 for m != 0; sum_i lam_i (-P_i[0] + strict_i) = 1
    rows = []
    for m in range(1, k):
        r = [P[i].get(m, Fraction(0)) for i in S]
        if any(r):
            rows.append((r, Fraction(0)))
    rows.append(([-P[i].get(0, Fraction(0)) + (1 if kinds[i] == 'gt' else 0) for i in S], Fraction(1)))
    fconst = sum(lam[i] * float(P[i].get(0, Fraction(0))) for i in S)
    if abs(fconst) < 1e-8:
        rows.append(([P[i].get(0, Fraction(0)) for i in S], Fraction(0)))
    n = len(S)
    # Gaussian elimination
    A = [list(r) + [b] for r, b in rows]
    piv = []
    row = 0
    for col in range(n):
        pr = next((j for j in range(row, len(A)) if A[j][col] != 0), None)
        if pr is None:
            continue
        A[row], A[pr] = A[pr], A[row]
        inv = 1 / A[row][col]
        A[row] = [a * inv for a in A[row]]
        for j in range(len(A)):
            if j != row and A[j][col] != 0:
                f = A[j][col]
                A[j] = [a - f * b for a, b in zip(A[j], A[row])]
        piv.append(col)
        row += 1
    for j in range(row, len(A)):
        if A[j][n] != 0:
            return None
    free = [c for c in range(n) if c not in piv]
    val = [None] * n
    for c in free:
        val[c] = Fraction(lam[S[c]]).limit_denominator(den) if den else Fraction(0)
    for r, c in enumerate(piv):
        val[c] = A[r][n] - sum(A[r][f] * val[f] for f in free)
    for c in range(n):
        if kinds[S[c]] != 'eq' and val[c] < 0:
            return None
    const = sum(val[c] * P[S[c]].get(0, Fraction(0)) for c in range(n))
    strict = sum(val[c] for c in range(n) if kinds[S[c]] == 'gt')
    if const > 0 or (const == 0 and strict <= 0):
        return None
    return [(S[c], val[c]) for c in range(n) if val[c] != 0]


def exact_cert(P, kinds, k, x, cols):
    for thr in (1e-7, 1e-9, 1e-5, 1e-11):
        for den in (10 ** 6, 10 ** 9, 10 ** 3, 0):
            c = exact_cert1(P, kinds, k, x, cols, thr, den)
            if c is not None:
                return c
    return None


def main():
    if sys.argv[1] == '--server':
        while True:
            hdr = sys.stdin.readline()
            if not hdr:
                return
            n, k = map(int, hdr.split())
            lines = [sys.stdin.readline() for _ in range(n + 1)]
            res = solve(n, k, iter(lines))
            sys.stdout.write(res + "\n")
            sys.stdout.flush()
    inp, out = sys.argv[1], sys.argv[2]
    with open(inp) as f:
        n, k = map(int, f.readline().split())
        res = solve(n, k, f)
    with open(out, 'w') as g:
        g.write(res + "\n")


def solve(n, k, f):
    if True:
        kinds = next(f).split()
        polys = []
        polys_exact = []
        for _ in range(n):
            t = next(f).split()
            c = int(t[0])
            p = {}
            pe = {}
            for j in range(c):
                m = int(t[1 + 2 * j])
                pe[m] = Fraction(t[2 + 2 * j])
                p[m] = float(pe[m])
            polys.append(p)
            polys_exact.append(pe)
    # variables: l_0..l_{n-1}; eq facts get two variables (pos/neg)
    cols = []
    for i in range(n):
        cols.append((i, 1.0))
        if kinds[i] == 'eq':
            cols.append((i, -1.0))
    nv = len(cols)
    # equality rows: monomials 1..k-1 coefficient zero; row k: -const + sum_strict l = 1
    A = lil_matrix((k, nv))
    for v, (i, sg) in enumerate(cols):
        for m, c in polys[i].items():
            if m == 0:
                continue
            A[m - 1, v] = sg * c
        A[k - 1, v] = -sg * polys[i].get(0, 0.0) + (1.0 if kinds[i] == 'gt' and sg > 0 else 0.0)
    b = np.zeros(k)
    b[k - 1] = 1.0
    # constant must be <= 0:  sum sg*l*const <= 0
    Aub = lil_matrix((1, nv))
    for v, (i, sg) in enumerate(cols):
        Aub[0, v] = sg * polys[i].get(0, 0.0)
    cost = np.ones(nv)
    res = linprog(cost, A_ub=Aub.tocsr(), b_ub=np.zeros(1), A_eq=A.tocsr(), b_eq=b,
                  bounds=(0, None), method='highs')
    if res.status != 0:
        return "FAIL"
    cert = exact_cert(polys_exact, kinds, k, res.x, cols)
    if cert is None:
        return "FAIL"
    return " ".join("%d %s" % (i, c) for i, c in cert)


if __name__ == '__main__':
    main()

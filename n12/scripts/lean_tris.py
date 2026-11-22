#!/usr/bin/env python3
"""Extract triangle_nonavoidance instances (points + affine weights) from a Lean file
and emit HOL tri_lemma definitions."""
import re, sys
from fractions import Fraction as Fr

def hol_num(s):
    s = s.strip().strip('()')
    f = Fr(s)
    if f.denominator == 1:
        return ("-- &%d" % -f.numerator) if f < 0 else ("&%d" % f.numerator)
    if f < 0:
        return "(-- &%d / &%d)" % (-f.numerator, f.denominator)
    return "&%d / &%d" % (f.numerator, f.denominator)

def hol_affine(e):
    # e like "(125/92)*X+0*Y+(-457/368)"  or "-1*X+(20/37)*Y+(196/185)"
    m = re.fullmatch(r'\s*(.+?)\*X\s*\+\s*(.+?)\*Y\s*\+\s*(.+?)\s*', e)
    a, b, c = (Fr(x.strip().strip('()')) for x in m.groups())
    def t(k, v):
        return "(%s) * %s" % (hol_num(str(k)), v)
    return "%s + %s + %s" % (t(a, "c1"), t(b, "c2"), hol_num(str(c)))

src = open(sys.argv[1]).read()
prefix = sys.argv[2]
defs = dict(re.findall(r'noncomputable def (\w+) \(X Y : ℝ\) : ℝ := (.*)', src))
out = []
for m in re.finditer(r'theorem (\w+)_hit \(q : OpenSquare\).*?exact triangle_nonavoidance q ha (.*?)\n\s*\((\w+) \(centerX q\) \(centerY q\)\) \((\w+) \(centerX q\) \(centerY q\)\) \((\w+) \(centerX q\)', src, re.S):
    name, pts, w0, w1, w2 = m.groups()
    toks = re.findall(r'\([^()]*\)|[^\s()]+', pts)
    assert len(toks) == 6, (name, toks)
    P = [hol_num(t) for t in toks]
    W = [hol_affine(defs[w]) for w in (w0, w1, w2)]
    out.append('let %s_%s = tri_lemma ((q"%s",q"%s"),(q"%s",q"%s"),(q"%s",q"%s"))\n  (q"%s",\n   q"%s",\n   q"%s");;'
               % (prefix, name.upper(), *P, *W))
print("\n".join(out))

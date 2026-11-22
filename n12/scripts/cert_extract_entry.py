#!/usr/bin/env python3
"""W-ENTRY extractor (untrusted): the ownership-domain data of the historical entries
(C701/713/717/973/978/979) from the Lean sources into n12/data/cert/.

Outputs:
  n12/data/cert/entry_queries.txt   one LocalQuery per line (the HistoricalOwnership queries and
                                the inline C713 queries; the Phase-1 ones are already in HOL
                                as LOCAL_QUERIES):
        name mask kind owned ins outs
     owned: '0,3' or '-' (empty);  ins/outs: 'x,y;x,y' rational points used by the
     certificate (hints only: HOL re-derives every membership and the contradiction)
  n12/data/cert/entry_cases.txt     the domain construction of every case, in Lean's order:
        F case m1,m2,...                         case family (Lean caseNNNFamily)
        S case name mask kind lo hi allowed      DirectSingleDomain (Check family kind)
        P case name single0 single1              CertifiedDomain.ofDirectProduct
        R case name src owned                    CertifiedDomain.remove (query of kind 2)
        A case name a b                          a.refineAgainst b
        E case name src allowed                  src.enlarge allowed
        C case name dom x,y W1 W2 ...            CertifiedPoint.ofDomainHull dom point ws
             W = mask:owned:p0x,p0y:p1x,p1y:p2x,p2y:tx,ty:s:t   (OwnedHullPoint)
        K case name1,name2,...                   commonPointsNNN (the 'known' list)
        O case k dom mask target inside outside  owner k: PointPremises.Check dom known
                                                  insideK outsideK; target = Lean domain
     sets: '0,3' or 'e' (empty), several separated by ';'
Usage: n12/scripts/cert_extract_entry.py
"""
import re, glob, os
from fractions import Fraction as Fr

LEAN = "n12/ext/jatloe/Lean/Proofs/N12-jatloe"
COMPACT = LEAN + "/Compact"
OUT = "n12/data/cert"
CASES = ["701", "713", "717", "973", "978", "979", "898"]

NUM = r'\(?-?\d+(?:/\d+)?\)?'
PT = r'\(\s*(' + NUM + r')\s*,\s*(' + NUM + r')\s*\)'


def fr(s):
    return Fr(s.replace('(', '').replace(')', ''))


def pts(s):
    return [(fr(a), fr(b)) for a, b in re.findall(PT, s)]


def transform(sw, rx, ry):
    def f(p):
        u, v = (p[1], p[0]) if sw else p
        return (4 - u if rx else u, 4 - v if ry else v)
    return f


B = lambda s: s == 'true'

# ---------------------------------------------------------------- local queries
four = {}
for f in glob.glob(LEAN + '/source/S12/FourPointData/*.lean'):
    for m in re.finditer(r'def fourDatum(\d+) : FourPointDatum := ⟨(' + PT + r'),(' + PT + r'),(' + PT + r'),(' + PT + r'),',
                         open(f).read()):
        g = m.groups()
        four[int(g[0])] = [pts(g[1])[0], pts(g[4])[0], pts(g[7])[0], pts(g[10])[0]]
SHORT_OUT = {'fiveLeft': [(1, Fr(87, 50)), (Fr(33, 20), Fr(47, 20)), (2, Fr(87, 50))],
             'fiveRight': [(1, Fr(87, 50)), (Fr(33, 20), Fr(47, 20)), (2, Fr(87, 50))],
             'six': [(1, Fr(8, 5)), (1, Fr(12, 5)), (Fr(33, 20), Fr(33, 20))]}

QREC = r'⟨(\d+),(\d+),(?:\{([\d,]*)\}|∅),\.(\w+) (.*)⟩\s*$'


def parse_setlit(s):
    s = s.strip()
    if s == '∅' or s == '{}':
        return []
    assert s[0] == '{' and s[-1] == '}', s
    return sorted(int(x) for x in s[1:-1].split(',') if x.strip())


def query_hints(typ, rest):
    if typ == 'hull':
        P = pts(rest)
        ins, outs = P[:3], [P[3]]
    elif typ == 'four':
        t = re.match(r'⟨(\w+),(\w+),(\w+)⟩ fourDatum(\d+)', rest).groups()
        T = transform(B(t[0]), B(t[1]), B(t[2]))
        a, b, p, e = four[int(t[3])]
        ins, outs = [T(a), T(b)], [T(p), T(e)]
    elif typ == 'short':
        t = re.match(r'⟨⟨(\w+),(\w+),(\w+)⟩,\.(\w+)⟩ \[(.*)\]', rest).groups()
        T = transform(B(t[0]), B(t[1]), B(t[2]))
        ins = []
        for w in t[4].strip('⟨⟩').split('⟩,⟨'):
            parts, depth, cur = [], 0, ''
            for ch in w:
                if ch == '(':
                    depth += 1
                elif ch == ')':
                    depth -= 1
                if ch == ',' and depth == 0:
                    parts.append(cur); cur = ''
                else:
                    cur += ch
            parts.append(cur)
            assert len(parts) == 6, w
            ins += [pts(x)[0] for x in parts[:3]]
        outs = [T(p) for p in SHORT_OUT[t[3]]]
    else:
        raise ValueError(typ)
    dd = lambda L: [p for i, p in enumerate(L) if p not in L[:i]]
    return dd(ins), dd(outs)


def rec_of(body):
    m = re.match(QREC, body.strip())
    assert m, body[:200]
    mask, kind, owned, typ, rest = m.groups()
    owned = sorted(int(x) for x in (owned or '').split(',') if x)
    ins, outs = query_hints(typ, rest)
    return (int(mask), int(kind), owned, ins, outs)


# Phase-1 queries (signatures only; HOL has them as LOCAL_QUERIES)
phase1 = {}
for f in sorted(glob.glob(LEAN + '/source/S12/LocalQueryDataChunks/*.lean')):
    for m in re.finditer(r'def localQuery(\d+) : LocalQuery := (⟨.*⟩)\n', open(f).read()):
        phase1[int(m.group(1))] = rec_of(m.group(2))
hist = {}
for f in sorted(glob.glob(COMPACT + '/HistoricalOwnership/Queries*.lean')):
    for m in re.finditer(r'checked_local_query query(\d+) := (⟨.*⟩)\n', open(f).read()):
        hist[int(m.group(1))] = rec_of(m.group(2))
inlq = {}        # inline case queries  def queryCCC_N : LocalQuery := ...  (C713, C898)
for c in CASES:
    for f in sorted(glob.glob(COMPACT + '/Cases/C%s/*.lean' % c)):
        for m in re.finditer(r'def query%s_(\d+) : LocalQuery := (.*)\n' % c, open(f).read()):
            body = m.group(2).strip()
            lm = re.match(r'localQuery(\d+)$', body)
            inlq[(c, int(m.group(1)))] = phase1[int(lm.group(1))] if lm else ('new', rec_of(body))
c979sel = {}
for f in sorted(glob.glob(COMPACT + '/Cases/C979/SharedSelections/*.lean')):
    for m in re.finditer(r'def selected(\d+) : \{q : LocalQuery // q.Check\} := \(certified_query% (\d+)\)', open(f).read()):
        c979sel[int(m.group(1))] = phase1[int(m.group(2))]
print('queries: phase1 %d, historical %d, inline %d (%d new), c979 selections %d' %
      (len(phase1), len(hist), len(inlq), sum(1 for v in inlq.values() if v[0] == 'new'), len(c979sel)))

fmt_q = lambda x: str(x.numerator) if x.denominator == 1 else '%d/%d' % (x.numerator, x.denominator)
fmt_p = lambda p: fmt_q(p[0]) + ',' + fmt_q(p[1])
fmt_pl = lambda L: ';'.join(fmt_p(p) for p in L) if L else '-'
fmt_set = lambda s: ','.join(map(str, s)) if s else 'e'
fmt_sets = lambda L: ';'.join(fmt_set(s) for s in L) if L else '-'

os.makedirs(OUT, exist_ok=True)
with open(OUT + '/entry_queries.txt', 'w') as fo:
    for i in sorted(hist):
        m, k, o, ins, outs = hist[i]
        fo.write('H%d %d %d %s %s %s\n' % (i, m, k, ','.join(map(str, o)) or '-', fmt_pl(ins), fmt_pl(outs)))
    for (c, i) in sorted(inlq):
        if inlq[(c, i)][0] == 'new':
            m, k, o, ins, outs = inlq[(c, i)][1]
            fo.write('C%s_%d %d %d %s %s %s\n' % (c, i, m, k, ','.join(map(str, o)) or '-', fmt_pl(ins), fmt_pl(outs)))


def query_sig(tok):
    """signature (mask, kind, owned) of a query reference in a .remove"""
    tok = tok.strip()
    m = re.match(r'\(certified_query% (\d+)\)$', tok)
    if m:
        return phase1[int(m.group(1))][:3]
    m = re.match(r'N12Compact\.HistoricalOwnership\.Queries\.query(\d+)_certified$', tok)
    if m:
        return hist[int(m.group(1))][:3]
    m = re.match(r'query(\d+)_(\d+)$', tok)
    if m:
        v = inlq[(m.group(1), int(m.group(2)))]
        return (v[1] if v[0] == 'new' else v)[:3]
    m = re.match(r'N12Compact\.C979SharedSelections\.selected(\d+)$', tok)
    if m:
        return c979sel[int(m.group(1))][:3]
    raise ValueError(tok)


def split_sets(s):
    """'[{2,12},∅,{3}]' -> [[2,12],[],[3]]"""
    s = s.strip()
    assert s[0] == '[' and s[-1] == ']', s
    return [parse_setlit(x) for x in re.findall(r'\{[\d,]*\}|∅', s[1:-1])]


# ---------------------------------------------------------------- cases
recs = []
stats = {}
for c in CASES:
    d = COMPACT + '/Cases/C' + c
    base = open(d + ('/EntryQueryBase.lean' if os.path.exists(d + '/EntryQueryBase.lean') else '/EntryDomains.lean')).read()
    fam = parse_setlit(re.search(r'def case%sFamily : Finset Nat := (\{[\d,]*\})' % c, base).group(1))
    recs.append('F %s %s' % (c, ','.join(map(str, fam))))
    files = [d + '/EntryQueries.lean'] + sorted(glob.glob(d + '/EntryQueryChunks/Chunk*.lean')) + [d + '/EntryDomains.lean']
    singles = {}
    for f in files:
        if not os.path.exists(f):
            continue
        t = open(f).read()
        for m in re.finditer(r'def (single%s_\d+_\d+) : DirectSingleDomain := ⟨(\d+),(\d+),(\d+),(\[[^\]]*\]),' % c, t):
            name, mask, lo, hi, al = m.groups()
            singles[name] = (int(mask), int(lo), int(hi), split_sets(al))
        for m in re.finditer(r'theorem (single%s_\d+_\d+)_checked : (single%s_\d+_\d+)\.Check case%sFamily (\d)' % (c, c, c), t):
            assert m.group(1) == m.group(2)
            singles[m.group(1)] = singles[m.group(1)] + (int(m.group(3)),)
    for name in sorted(singles, key=lambda n: [int(x) for x in n.split('_')[1:]]):
        mask, lo, hi, al, k = singles[name]
        recs.append('S %s %s %d %d %d %d %s' % (c, name, mask, k, lo, hi, fmt_sets(al)))
    ndom = {'P': 0, 'R': 0, 'A': 0, 'E': 0}
    for f in [d + '/EntryDomains.lean', d + '/EntryRefined.lean']:
        for line in open(f):
            m = re.match(r'def (\w+) : CertifiedDomain case%sFamily := (.*)$' % c, line.strip())
            if not m:
                continue
            name, body = m.groups()
            mp = re.match(r'\.ofDirectProduct _ (\w+) (\w+) ', body)
            mr = re.match(r'(?:N12Compact\.SharedLocalQueries\.remove|\.remove) _ (\w+) (\(certified_query% \d+\)|[\w.]+)', body)
            ma = re.match(r'(\w+)\.refineAgainst (\w+) ', body)
            me = re.match(r'(\w+)\.enlarge (\[.*\]) \(by', body)
            if mp:
                recs.append('P %s %s %s %s' % (c, name, mp.group(1), mp.group(2))); ndom['P'] += 1
            elif mr:
                src, q = mr.groups()
                sig = query_sig(q)
                recs.append('R %s %s %s %s %d %d' % (c, name, src, fmt_set(sig[2]), sig[0], sig[1])); ndom['R'] += 1
            elif ma:
                recs.append('A %s %s %s %s' % (c, name, ma.group(1), ma.group(2))); ndom['A'] += 1
            elif me:
                recs.append('E %s %s %s %s' % (c, name, me.group(1), fmt_sets(split_sets(me.group(2))))); ndom['E'] += 1
            else:
                raise ValueError(line[:200])
    # common points
    t = open(d + '/EntryPoints.lean').read()
    values = {}
    for m in re.finditer(r'def (commonPoint%s_\d+Value\d+) : OwnedHullPoint := ⟨(\d+),(\{[\d,]*\}|∅),\(⟨(.*)⟩\)⟩\n' % c, t):
        name, mask, owned, tri = m.groups()
        mst = re.match(r'^(?:\s*' + PT + r'\s*,){4}\s*(' + NUM + r')\s*,\s*(' + NUM + r')\s*$', tri)
        assert mst, tri
        st = mst.groups()[-2:]
        P = pts(tri)[:4]
        values[name] = (int(mask), parse_setlit(owned), P, fr(st[0]), fr(st[1]))
    witn = {}
    for m in re.finditer(r'def (commonPoint%s_\d+)Witnesses : List \{w : OwnedHullPoint // w.Check case%sFamily\} := \[(.*)\]\n' % (c, c), t):
        witn[m.group(1)] = re.findall(r'⟨(commonPoint%s_\d+Value\d+),\1_checked⟩' % c, m.group(2))
    npt = 0
    for m in re.finditer(r'def (commonPoint%s_\d+) : CertifiedPoint case%sFamily := \.ofDomainHull (\w+) \(by decide \+kernel\) \((' % (c, c)
                         + NUM + r'),(' + NUM + r')\) (\w+) \(by decide \+kernel\)', t):
        name, dom, x, y, wl = m.groups()
        assert wl == name + 'Witnesses'
        ws = []
        for v in witn[name]:
            mask, owned, P, s, tt = values[v]
            ws.append('%d:%s:%s:%s:%s:%s:%s:%s' % (mask, fmt_set(owned), fmt_p(P[0]), fmt_p(P[1]), fmt_p(P[2]),
                                                   fmt_p(P[3]), fmt_q(s), fmt_q(tt)))
        recs.append('C %s %s %s %s %s' % (c, name, dom, fmt_p((fr(x), fr(y))), ' '.join(ws)))
        npt += 1
    known = re.search(r'def commonPoints%s : List \(CertifiedPoint case%sFamily\) := \[(.*)\]' % (c, c), t).group(1)
    recs.append('K %s %s' % (c, known.replace(' ', '')))
    # owners: inside/outside lists and the entries
    t = open(d + ('/RecipeInitial/Inputs.lean' if os.path.exists(d + '/RecipeInitial/Inputs.lean') else '/DirectInitial/Inputs.lean')).read()
    lists = {}
    for m in re.finditer(r'def (inside|outside)(\d+) : List \(ℚ × ℚ\) := \[(.*)\]\n', t):
        lists[(m.group(1), int(m.group(2)))] = pts(m.group(3))
    t = open(d + '/RecipeInitial/Entry.lean').read()
    nown = 0
    for m in re.finditer(r'PointPremises\.Check (case%sDomain\d+) commonPoints%s inside(\d+) outside(\d+) := by' % (c, c), t):
        dom, k1, k2 = m.groups()
        assert k1 == k2
        k = int(k1)
        mm = re.search(r'theorem owner%d_cover .*?OrientedPoseCovered\s+([\w.]+)\s*\(p\.square \(ownerIndex p (\d+)\)\)' % k, t, re.S)
        target, mask = mm.group(1).split('.')[-1], int(mm.group(2))
        recs.append('O %s %d %s %d %s %s %s' % (c, k, dom, mask, target, fmt_pl(lists[('inside', k)]),
                                                fmt_pl(lists[('outside', k)])))
        nown += 1
    stats[c] = (len(singles), ndom, npt, nown)
    print('C%s: %d singles, domains %s, %d common points, %d owners' % (c, len(singles), ndom, npt, nown))

with open(OUT + '/entry_cases.txt', 'w') as fo:
    fo.write('\n'.join(recs) + '\n')
print('wrote', OUT + '/entry_queries.txt', OUT + '/entry_cases.txt', len(recs), 'records')

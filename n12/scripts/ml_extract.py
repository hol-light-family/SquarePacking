#!/usr/bin/env python3
"""Extract MergedLower (families 71,80,589,590) and Endpoint684 domain data as OCaml
(type xdom of n12/geometry/bridge_ext.ml).  Output: ML_CASES : (int * int list * (int * xdom) list) list."""
import re, sys
base = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Cases/'
def fset(s):
    s = s.strip()
    if s in ('∅', '{}'): return []
    return sorted(int(x) for x in s.strip('{}').split(',') if x.strip())
def pt(x):
    a, b = x.strip().strip('()').split(',')
    return '(qn"%s",qn"%s")' % (a.strip('()'), b.strip('()'))
def split_top(tri):
    parts, depth, cur = [], 0, ''
    for ch in tri:
        if ch == '(': depth += 1
        elif ch == ')': depth -= 1
        if ch == ',' and depth == 0: parts.append(cur); cur = ''
        else: cur += ch
    parts.append(cur); return parts
def tri_ml(tri):
    p = split_top(tri)
    return '([%s],%s,qn"%s",qn"%s")' % ('; '.join(pt(x) for x in p[:3]), pt(p[3]), p[4].strip(), p[5].strip())
def dom(body):
    m = re.match(r'\s*direct \w+ combinedSpec(\d+)', body)
    if m: return 'Xrcomb %s' % m.group(1)
    m = re.match(r'\s*reflected \w+ (\d+) combinedSpec(\d+)', body)
    if m: return 'Xrtr(%s,(false,true,false))' % m.group(2)
    m = re.match(r'\s*halfturned \w+ (\d+) combinedSpec(\d+)', body)
    if m: return 'Xrtr(%s,(false,true,true))' % m.group(2)
    if 'OwnerBudget.product' in body:
        m1 = re.search(r'ofSingle \w+ singleSpec(\d+) singleSpec\d+_checked (\d)', body)
        m2 = re.search(r'ofSmallBudgetWithSeed \w+ \d+ (\d) \(by decide \+kernel\)\s*(\d+) \(by decide \+kernel\)\s*⟨(.*?)⟩', body, re.S)
        if m1 and m2:
            return 'Xpprod(Prspec(%s,%s),Prsmall(%s,%s,%s))' % (m1.group(1), m1.group(2), m2.group(1), m2.group(2), tri_ml(m2.group(3)))
    raise SystemExit('unknown domain: ' + body[:200])
out = ['let ML_CASES = [']
def emit(cid, src, famname, dompat, listname):
    fam = fset(re.search(r'def %s : Finset Nat :=\s*(\{[^}]*\})' % famname, src).group(1))
    doms = {}
    for m in re.finditer(r'def %s : CertifiedDomain %s :=\s*(.*?)\n\n' % (dompat, famname), src, re.S):
        doms[m.group(1)] = dom(m.group(2))
    order = re.search(r'def %s : List \(CertifiedDomain %s\) :=\s*\[(.*?)\]' % (listname, famname), src, re.S).group(1)
    order = [x.strip() for x in order.split(',')]
    def mask_of(name):
        return int(re.search(r'(\d+)$', name).group(1))
    out.append('  (%d, [%s], [%s]);' % (cid, '; '.join(map(str, fam)),
        '; '.join('(%d, %s)' % (mask_of(n), doms[n]) for n in order)))
s1 = open(base + 'MergedLower/Domains7180.lean').read()
s2 = open(base + 'MergedLower/Domains589590.lean').read()
for cid, src in [(71, s1), (80, s1), (589, s2), (590, s2)]:
    emit(cid, src, 'family%d' % cid, r'(domain%d_\d+)' % cid, 'domains%d' % cid)
s3 = open(base + 'Endpoint684.lean').read()
emit(684, s3, 'family', r'(domain\d+)', 'domains')
out.append('];;')
print('\n'.join(out))

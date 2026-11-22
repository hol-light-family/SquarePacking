#!/usr/bin/env python3
"""Extract the 15 FourSquare cases (Compact/Cases/FourSquare/Case*.lean) as OCaml data."""
import re, glob, sys
famname = sys.argv[1] if len(sys.argv) > 1 else 'FourSquare'
# optional 3rd arg 'x': extended output for n12/geometry/bridge_ext.ml (type xdom, promotion field)
XMODE = len(sys.argv) > 3 and sys.argv[3] == 'x'
def split_top(tri):
    parts, depth, cur = [], 0, ''
    for ch in tri:
        if ch == '(': depth += 1
        elif ch == ')': depth -= 1
        if ch == ',' and depth == 0: parts.append(cur); cur = ''
        else: cur += ch
    parts.append(cur)
    return parts
def pt(x):
    a, b = x.strip().strip('()').split(',')
    return '(qn"%s",qn"%s")' % (a.strip('()'), b.strip('()'))
def tri_ml(tri):
    parts = split_top(tri)
    return '([%s],%s,qn"%s",qn"%s")' % ('; '.join(pt(x) for x in parts[:3]), pt(parts[3]),
                                        parts[4].strip(), parts[5].strip())
base = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Cases/' + famname + '/'
def fset(s):
    s = s.strip()
    if s in ('∅', '{}'): return []
    return sorted(int(x) for x in s.strip('{}').split(',') if x.strip())
out = ['let %s = [' % (sys.argv[2] if len(sys.argv) > 2 else 'FS_CASES')]
for f in sorted(glob.glob(base + 'Case*.lean')):
    src = open(f).read()
    cid = int(re.search(r'Case(\d+)\.lean', f).group(1))
    fam = fset(re.search(r'def family\d+ : Finset Nat := (\{[^}]*\})', src).group(1))
    doms = {}
    for m in re.finditer(r'def domain\d+_(\d+) : CertifiedDomain family\d+ :=\s*(.*?)\n\n', src, re.S):
        mask = int(m.group(1)); body = m.group(2)
        if XMODE and 'UpperMidDomain.domain33792' in body: doms[mask] = 'Xd(Dcomb 2002)'; continue
        if XMODE and re.match(r'\s*promotion\d+\.combined', body):
            doms[mask] = 'Xpcomb %d' % int(re.search(r'combinedSpec(\d+)', body).group(1)); continue
        if XMODE and 'OwnerBudget.product' in body and 'promotion' in body:
            halves = re.findall(r'\((?:HalfDomain\.(\w+) family\d+|promotion\d+\.(\w+)) ?(.*?)\)\s*(?=\(HalfDomain|\(promotion|$)', body, re.S)
            hs = []
            for hk, pk, args in halves:
                if pk == 'ofSpec':
                    n, k = re.match(r'singleSpec(\d+) (\d)', args).groups(); hs.append('Phspec(%s,%s)' % (n, k))
                elif pk == 'ownDomain': hs.append('Phown %s' % args.strip())
                elif pk == 'singleton': hs.append('Phsing %s' % re.match(r'\d+ (\d)', args).group(1))
                elif hk == 'ofSpec':
                    n, k = re.match(r'singleSpec(\d+) (\d)', args).groups(); hs.append('Ph(Hspec(%s,%s))' % (n, k))
                elif hk == 'singleton': hs.append('Ph(Hsing %s)' % re.match(r'\d+ (\d)', args).group(1))
                else: raise SystemExit('unknown promoted half %s%s' % (hk, pk))
            doms[mask] = 'Xpprod(%s,%s)' % (hs[0], hs[1]); continue
        if 'CornerPairDomain.domain520' in body: doms[mask] = 'Dcomb 2000'
        elif 'CornerPairDomain.domain2112' in body: doms[mask] = 'Dcomb 2001'
        elif 'ofCombined' in body:
            n = int(re.search(r'combinedSpec(\d+)', body).group(1))
            doms[mask] = 'Dcomb %d' % n
        elif 'OwnerBudget.product' in body:
            halves = re.findall(r'\(HalfDomain\.(\w+) family\d+ (.*?)\)\s*(?=\(HalfDomain|$)', body, re.S)
            hs = []
            for kind, args in halves:
                if kind == 'ofSpec':
                    n, k = re.match(r'singleSpec(\d+) (\d)', args).groups()
                    hs.append('Hspec(%s,%s)' % (n, k))
                elif kind == 'singleton':
                    k = re.match(r'\d+ (\d)', args).group(1)
                    hs.append('Hsing %s' % k)
                elif kind == 'ofSeedHull':
                    mm = re.match(r'family\d+ (\d+) (\d) (\d+)', 'family0 ' + args)
                    k, idx = mm.group(2), mm.group(3)
                    tri = re.search(r'⟨(.*?)⟩', args).group(1)
                    parts, depth, cur = [], 0, ''
                    for ch in tri:
                        if ch == '(': depth += 1
                        elif ch == ')': depth -= 1
                        if ch == ',' and depth == 0: parts.append(cur); cur = ''
                        else: cur += ch
                    parts.append(cur)
                    def pt(x):
                        a, b = x.strip().strip('()').split(',')
                        return '(qn"%s",qn"%s")' % (a.strip('()'), b.strip('()'))
                    hs.append('Hhull(%s,%s,([%s],%s,qn"%s",qn"%s"))' % (k, idx, '; '.join(pt(x) for x in parts[:3]),
                              pt(parts[3]), parts[4].strip(), parts[5].strip()))
                else:
                    raise SystemExit('unknown half ' + kind)
            doms[mask] = 'Dprod(%s,%s)' % (hs[0], hs[1])
        else:
            doms[mask] = None
        if XMODE and doms[mask] is not None: doms[mask] = 'Xd(%s)' % doms[mask]
        if False:
            doms[mask] = None
    if None in doms.values():
        sys.stderr.write('skip case %d: unknown domain\n' % cid); continue
    order = re.search(r'def domains\d+ : List \(CertifiedDomain family\d+\) :=\s*\[(.*?)\]', src, re.S).group(1)
    order = [int(x) for x in re.findall(r'domain\d+_(\d+)', order)]
    d = re.search(r'def data\d+ : [\w.]+ :=\s*⟨⟨(\w+),(\w+),(\w+)⟩, !\[([\d,]*)\],\s*!\[(.*?)\], (\d+)(?:, (\d+))?(,.*?)?⟩\n', src, re.S)
    tr = tuple(x == 'true' for x in d.groups()[:3])
    masks = [int(x) for x in d.group(4).split(',')]
    owned = [fset(x) for x in re.findall(r'\{[\d,]*\}|∅', d.group(5))]
    lb, rb = int(d.group(6)), int(d.group(7) or -1)
    if d.group(8) and d.group(8).strip(', \n') != '![[],[],[],[],[]]': sys.stderr.write('case %d extra data: %s\n' % (cid, d.group(8)))
    ol = lambda l: '[' + '; '.join(map(str, l)) + ']'
    promo = ''
    if XMODE:
        pm = re.search(r'def promotion\d+ : Promotion family\d+ :=\s*⟨(\d+),.*?\(fun _ => (\d+)\), !\[⟨(.*?)⟩,⟨(.*?)⟩\]', src, re.S)
        promo = ', None' if not pm else ', Some(%s, [(%s, %s); (%s, %s)])' % (
            pm.group(1), pm.group(2), tri_ml(pm.group(3)), pm.group(2), tri_ml(pm.group(4)))
        if 'promotion' in src and not pm: raise SystemExit('promotion not parsed in %d' % cid)
    out.append('  (%d, %s, [%s], (%s), %s, [%s], %d, %d%s);' % (
        cid, ol(fam), '; '.join('(%d, %s)' % (m, doms[m]) for m in order),
        ', '.join('true' if b else 'false' for b in tr), ol(masks),
        '; '.join(ol(o) for o in owned), lb, rb, promo))
out.append('];;')
print('\n'.join(out))

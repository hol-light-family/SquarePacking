import re, sys
L = 'n12/ext/jatloe/Lean/Proofs/N12-jatloe/Compact/Completion/OtherCases/C983/'
def sets(s):  # "{2},{0,2}" -> [[2],[0,2]]
    return [[int(x) for x in g.split(',') if x.strip()] for g in re.findall(r'\{([^{}]*)\}', s)]
def setl(s):
    s = s.strip()
    if s == '∅': return []
    return [int(x) for x in s.strip('{}').split(',') if x.strip()]
def ol(l): return '[' + '; '.join(str(x) for x in l) + ']'
def oll(l): return '[' + '; '.join(ol(x) for x in l) + ']'
def tl(l): return '`[' + '; '.join('{' + ','.join(map(str, x)) + '}' if x else '{}' for x in l) + ']`'
for nn in sys.argv[1:]:
    src = open(L + 'Components%s.lean' % nn).read()
    n = str(int(nn)); tag = 'c983c%s' % nn; TAG = tag.upper()
    def body(name):
        m = re.search(r'def %s[^=]*:=\s*(.*?)(?=\n\s*\n|\nprivate|\ndef|\nend)' % name, src, re.S)
        return m.group(1)
    def queries(name):
        b = body(name)
        if b.strip() == '[]': return []
        qs = re.findall(r'certified_query% (\d+)', b)
        assert len(qs) == b.count('('), name
        return [int(q) for q in qs]
    def sigs(name):
        b = body(name)
        out = []
        for t in re.findall(r'\((\d+),(\d+),(\{[^}]*\}|∅),(\{[^}]*\}|∅)\)', b):
            out.append((int(t[0]), int(t[1]), setl(t[2]), setl(t[3])))
        assert len(out) == b.count('('), name
        return out
    def single(name):
        m = re.search(r'def %s : SingleDomain :=\s*⟨(\d+),(\d+),(\d+),\[(.*?)\],(\w+)⟩' % name, src, re.S)
        return int(m.group(1)), int(m.group(2)), int(m.group(3)), sets(m.group(4)), m.group(5)
    def cache(name):
        m = re.search(r'def %s[^⟨]*?:=\s*⟨?DomainTransport\.cache (\w+) (\d+)\s*\[(.*?)\] \(by rfl\)' % name, src, re.S)
        return m.group(1), int(m.group(2)), sets(m.group(3))
    fq, gq, cq = queries('fQueries' + n), queries('gQueries' + n), queries('combinedQueries' + n)
    fs, gs, cs = sigs('fSignatures' + n), sigs('gSignatures' + n), sigs('combinedSignatures' + n)
    fd, gd = single('fSingle' + n), single('gSingle' + n)
    assert fd[4] == 'fQueries' + n and gd[4] == 'gQueries' + n
    assert re.search(r'product family fSingle%s gSingle%s fSignatures%s gSignatures%s\s*fExact%s gExact%s fChecked%s gChecked%s \(by rfl\)' % ((n,)*8), src)
    assert re.search(r'fSingle%s\.Check family 0 fSignatures%s' % (n, n), src)
    assert re.search(r'gSingle%s\.Check family 1 gSignatures%s' % (n, n), src)
    assert re.search(r'diameterFilter \(trim cachedProduct%s combinedQueries%s combinedSignatures%s combinedExact%s\)' % ((n,)*4), src)
    c1, c1m, c1al = cache('cachedProduct' + n); assert c1 == 'rawDomain' + n
    c2, c2m, c2al = cache('initial' + n); assert c2 == 'filtered' + n
    doc = re.search(r'/-!(.*?)-/', src, re.S).group(1).strip().split('\n')
    def sigtxt(l): return '[' + ';\n   '.join('(%d, %d, %s, %s)' % (a, b, ol(c), ol(d)) for a, b, c, d in l) + ']'
    def dsd(d, q): return '{dmask = %d; dlower = %d; dupper = %d; dallowed = %s; dqueries = %s}' % (d[0], d[1], d[2], oll(d[3]), q)
    o = []
    o.append('(* ========================================================================= *)')
    o.append('(* Phase 2: Compact/Completion/OtherCases/C983/Components%s.lean.           *)' % nn)
    for d in doc: o.append('(* ' + d.strip().ljust(73) + ' *)')
    o.append('(* Lean certified_query% n = local query n (slq_data / mq_signature);      *)')
    o.append('(* SingleDomain = dsd record, Check = mq_single, product = mq_product,      *)')
    o.append('(* trim = mr_trim, diameterFilter = mr_diameter_filter, cache = dc_cache,   *)')
    o.append('(* NamedDomain = (|- cdom fam m al, |- m IN fam) via dt_named.              *)')
    o.append('(* family = c983ri_family (C983/RowIdentity).                               *)')
    o.append('(* ========================================================================= *)')
    o.append('')
    o.append('needs "n12/geometry/CP_OtherCases_C983_RowIdentity.ml";;')
    o.append('needs "n12/geometry/CP_OtherCases_MonotoneRefinement.ml";;')
    o.append('needs "n12/geometry/CP_OtherCases_DomainCache.ml";;')
    o.append('needs "n12/geometry/SharedLocalQueries.ml";;')
    o.append('')
    o.append('(* Lean signatures = queries.map signature (the fExact / gExact decides) *)')
    o.append('let %s_exact sigs qs =' % tag)
    o.append('  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in')
    o.append('  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "%s_exact";;' % tag)
    o.append('')
    for (pre, q, s) in [('f', fq, fs), ('g', gq, gs)]:
        o.append('(* Lean: %sQueries%s (private) *)' % (pre, n))
        o.append('let %s_%squeries = %s;;' % (tag, pre, ol(q)))
        o.append('(* Lean: %sSignatures%s (private) *)' % (pre, n))
        o.append('let %s_%ssignatures =\n  %s;;' % (tag, pre, sigtxt(s)))
        o.append('(* Lean: %sExact%s (private) *)' % (pre, n))
        o.append('let () = %s_exact %s_%ssignatures %s_%squeries;;' % (tag, tag, pre, tag, pre))
        d = fd if pre == 'f' else gd
        o.append('(* Lean: %sSingle%s (private) *)' % (pre, n))
        o.append('let %s_%ssingle =\n  %s;;' % (tag, pre, dsd(d, '%s_%squeries' % (tag, pre))))
        o.append('')
    o.append('(* Lean: fChecked%s, gChecked%s, rawDomain%s (private): the two half domains      *)' % (n, n, n))
    o.append('(* (kinds 0 and 1) and their product  |- cdom c983ri_family %d [..]          *)' % fd[0])
    o.append('let %s_FCHECKED = mq_single `c983ri_family` 0 %s_fsingle;;' % (TAG, tag))
    o.append('let %s_GCHECKED = mq_single `c983ri_family` 1 %s_gsingle;;' % (TAG, tag))
    o.append('let %s_RAW_DOMAIN =' % TAG)
    o.append('  if %s_fsingle.dmask <> %s_gsingle.dmask then failwith "%s: masks" else' % (tag, tag, tag))
    o.append('  pk_product %s_FCHECKED %s_GCHECKED;;' % (TAG, TAG))
    o.append('')
    o.append('(* Lean: cachedProduct%s (private) *)' % n)
    o.append('let %s_CACHED_PRODUCT = dc_cache %s_RAW_DOMAIN %d\n  %s;;' % (TAG, TAG, c1m, tl(c1al)))
    o.append('')
    o.append('(* Lean: combinedQueries%s, combinedSignatures%s, combinedExact%s (private) *)' % (n, n, n))
    o.append('let %s_combinedqueries : int list = %s;;' % (tag, ol(cq)))
    o.append('let %s_combinedsignatures : (int * int * int list * int list) list = %s;;' % (tag, sigtxt(cs)))
    o.append('let () = %s_exact %s_combinedsignatures %s_combinedqueries;;' % (tag, tag, tag))
    o.append('')
    o.append('(* Lean: filtered%s (private) *)' % n)
    o.append('let %s_FILTERED = mr_diameter_filter (mr_trim %s_CACHED_PRODUCT %s_combinedqueries);;' % (TAG, TAG, tag))
    o.append('')
    o.append('(* Lean: initial%s *)' % n)
    o.append('let %s_INITIAL = dt_named (dc_cache %s_FILTERED %d\n  %s);;' % (TAG, TAG, c2m, tl(c2al)))
    p = 'n12/geometry/CP_OtherCases_C983_Components%s.ml' % nn
    open(p, 'w').write('\n'.join(o) + '\n')
    print(p)

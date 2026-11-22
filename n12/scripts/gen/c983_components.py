import re, sys
lean_path, hol_name, tag, modname = sys.argv[1:5]
src = open(lean_path).read()
ns = re.search(r'namespace (\S+)', src).group(1)
imports = re.findall(r'^import (\S+)', src, re.M)
def needs_of(imp):
    p = imp.split('.')
    if p[0] != 'Compact': raise Exception(imp)
    if p[1] == 'HistoricalOwnership': return 'n12/geometry/%s.ml' % p[2]
    if p[1] == 'Bridge': return 'n12/geometry/%s.ml' % p[2]
    if p[1] == 'Completion': return 'n12/geometry/CP_%s.ml' % '_'.join(p[2:])
    raise Exception(imp)
def setl(s):
    s = s.strip()
    if s == '∅': return []
    return [int(x) for x in s.strip('{}').split(',') if x]
def ocl(l): return '[' + '; '.join(map(str, l)) + ']'
def holset(l): return '{' + ','.join(map(str, l)) + '}' if l else '({}:num->bool)'
def queries(body):
    out = []
    for it in re.findall(r'\(certified_query% (\d+)\)|Queries\.query(\d+)_certified', body):
        out.append(it[0] if it[0] else 'slq_hist_idx %s' % it[1])
    return out
def sigs(body):
    return [(int(m), int(k), setl(a), setl(b)) for m, k, a, b in
            re.findall(r'\((\d+),(\d+),(∅|\{[\d,]*\}),(∅|\{[\d,]*\})\)', body)]
def splitsets(s):
    return [setl(x) for x in re.findall(r'∅|\{[\d,]*\}', s)]
lines = []
hdr = ("(* ========================================================================= *)\n"
       "(* Phase 2: %s\n   (namespace %s).\n"
       "   Lean certified_query%% n = local query n (slq_data / mq_signature);\n"
       "   N12Compact.HistoricalOwnership.Queries.queryN_certified = historical query N\n"
       "   (HOQ_QUERYN of QueriesNNN.ml), referred to by index slq_hist_idx N;\n"
       "   signature = mq_signature (the Exact decides are the OCaml check %s_exact);\n"
       "   SingleDomain = dsd record, Check = mq_single, product = pk_product of the two\n"
       "   half domains, trim = mr_trim, diameterFilter = mr_diameter_filter,\n"
       "   DomainTransport.cache = dc_cache, NamedDomain = dt_named.\n"
       "   family = c983ri_family (C983/RowIdentity).  Tag %s_ / %s_.  *)\n"
       "(* ========================================================================= *)\n"
       ) % (lean_path.split('N12-jatloe/')[1], ns, tag.lower(), tag.lower(), tag.upper())
lines.append(hdr)
for imp in imports:
    lines.append('needs "%s";;' % needs_of(imp))
lines.append('')
t = tag.lower(); T = tag.upper()
lines.append("""(* Lean signatures = queries.map signature (the Exact decides) *)
let %s_exact sigs qs =
  let norm (m, k, ow, bl) = (m, k, List.sort compare ow, List.sort compare bl) in
  if map norm sigs <> map (fun q -> norm (mq_signature q)) qs then failwith "%s_exact";;
""" % (t, t))
# iterate over defs/theorems in order
items = re.finditer(r'((?:private )?)(def|theorem) (\w+)\s*:(.*?):=(.*?)(?=\n(?:private )?(?:def|theorem) |\nend)', src, re.S)
known = {}
STYLE01 = modname == 'c01'
def snake(n):
    n = re.sub(r'\d+$', '', n)
    return re.sub(r'(?<!^)(?=[A-Z])', '_', n).upper()
def hname(n):
    return '%s_%s' % (t, snake(n).lower()) if STYLE01 else '%s_%s' % (t, n)
def tname(n):
    return T + '_' + (snake(n) if STYLE01 else n.upper())
for m in items:
    priv, kind, name, ty, body = m.groups()
    pv = ' (private)' if priv else ''
    lines.append('(* Lean: %s%s *)' % (name, pv))
    if 'List {q : LocalQuery' in ty:
        qs = queries(body)
        lines.append('let %s : int list = [%s];;' % (hname(name), '; '.join(qs)))
    elif 'List Signature' in ty:
        ss = sigs(body)
        lines.append('let %s : (int * int * int list * int list) list =\n  [%s];;' % (hname(name), ';\n   '.join('(%d, %d, %s, %s)' % (a, b, ocl(c), ocl(d)) for a, b, c, d in ss)))
    elif re.search(r'Exact\d*$', name):
        mm = re.search(r'(\w+)=(\w+)\.map', ty.replace(' ', ''))
        lines.append('let () = %s_exact %s %s;;' % (t, hname(mm.group(1)), hname(mm.group(2))))
    elif 'SingleDomain' in ty:
        mm = re.search(r'⟨(\d+),(\d+),(\d+),\[(.*)\],(\w+)⟩', body, re.S)
        mask, lo, hi, al, qn = mm.groups()
        lines.append('let %s =\n  {dmask = %s; dlower = %s; dupper = %s; dallowed = [%s]; dqueries = %s};;' %
                     (hname(name), mask, lo, hi, '; '.join(ocl(x) for x in splitsets(al)), hname(qn)))
    elif 'Check family' in ty:
        mm = re.search(r'(\w+)\.Check family (\d+) (\w+)', ty)
        single, k, sg = mm.groups()
        lines.append('let %s = mq_single `c983ri_family` %s %s;;' % (tname(name), k, hname(single)))
        known[name] = tname(name)
        known[single + '#k'] = k
    elif 'CertifiedDomain' in ty or 'NamedDomain' in ty:
        b = ' '.join(body.split())
        if b.startswith('product family'):
            args = b.split()
            f, g = args[2], args[3]
            fc, gc = args[8], args[9]
            lines.append('let %s =\n  if %s.dmask <> %s.dmask then failwith "%s: masks" else\n  pk_product %s %s;;' %
                         (tname(name), hname(f), hname(g), t, known[fc], known[gc]))
        elif b.startswith('DomainTransport.cache'):
            mm = re.match(r'DomainTransport\.cache (\w+) (\d+) \[(.*?)\]', b)
            src_, mask, al = mm.groups()
            lines.append('let %s = dc_cache %s %s\n  `[%s]`;;' % (tname(name), known[src_], mask,
                         '; '.join(holset(x) for x in splitsets(al))))
        elif b.startswith('diameterFilter (trim'):
            mm = re.match(r'diameterFilter \(trim (\w+) (\w+) (\w+) (\w+)\)', b)
            c, qn = mm.group(1), mm.group(2)
            lines.append('let %s = mr_diameter_filter (mr_trim %s %s);;' % (tname(name), known[c], hname(qn)))
        elif b.startswith('⟨DomainTransport.cache'):
            mm = re.match(r'⟨DomainTransport\.cache (\w+) (\d+) \[(.*?)\]', b)
            src_, mask, al = mm.groups()
            lines.append('let %s = dt_named (dc_cache %s %s\n  `[%s]`);;' % (tname(name), known[src_], mask,
                         '; '.join(holset(x) for x in splitsets(al))))
        else:
            raise Exception('unknown body ' + b[:80])
        known[name] = tname(name)
    else:
        raise Exception('unknown item %s : %s' % (name, ty))
open('n12/geometry/%s.ml' % hol_name, 'w').write('\n'.join(lines) + '\n')

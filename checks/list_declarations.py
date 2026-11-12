"""List the development's declarations and flag any that could change name resolution of the
Challenge statements inside `namespace Erdos361.Statement` (Lean tries Erdos361.Statement.x,
then Erdos361.x, then the root and opened namespaces).
Usage: python3 -I list_declarations.py <project root>"""
import glob, os, re, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _common import strip_comments, read

root = sys.argv[1] if len(sys.argv) > 1 else '.'
kw = (r'(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+|partial\s+|@\[[^\]]*\]\s*)*'
      r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom|example)\s+([^\s:({\[⦃]+)?')
decls, exports = [], []
for f in sorted(glob.glob(os.path.join(root, 'Erdos361', '*.lean'))):
    stack = []
    for line in strip_comments(read(f)).split('\n'):
        t = line.strip()
        m = re.match(r'namespace\s+(\S+)', t)
        if m: stack.append(('ns', m.group(1))); continue
        m = re.match(r'section\b\s*(\S*)', t)
        if m: stack.append(('sec', m.group(1))); continue
        if re.match(r'end\b', t) and stack: stack.pop(); continue
        if re.match(r'export\b', t): exports.append((os.path.basename(f), t))
        m = re.match(kw, t)
        if m and m.group(2):
            ns = '.'.join(x[1] for x in stack if x[0] == 'ns'); nm = m.group(2)
            full = nm[7:] if nm.startswith('_root_.') else (ns + '.' + nm if ns else nm)
            decls.append((os.path.basename(f), m.group(1), full))
print('declarations found:', len(decls))
print('by top-level namespace:', dict(Counter(n.split('.')[0] if '.' in n else '<root>' for _, _, n in decls)))
idents = {'F', 'Fc', 'Avoids', 'Avoiders', 'Tendsto', 'atTop', 'nhds', 'Icc', 'card', 'Finset', 'Real', 'Nat'}
risky = ('Filter.', 'Topology.', 'Pointwise.', 'Erdos361.Statement.', 'Finset.', 'Nat.', 'Real.')
print('flagged (opened/parent namespace, or a statement identifier as last component):')
for f, k, n in decls:
    if n.startswith(risky) or n.split('.')[-1] in idents:
        print('   ', f, k, n)
print('root-level declarations:', [n for _, _, n in decls if '.' not in n])
print('export commands:', exports)

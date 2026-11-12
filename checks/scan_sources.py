"""Scan the development for constructs that could weaken a successful build.
Usage: python3 -I scan_sources.py <project root>"""
import glob, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _common import strip_comments, read

root = sys.argv[1] if len(sys.argv) > 1 else '.'
files = sorted(glob.glob(os.path.join(root, 'Erdos361', '*.lean'))) + \
        [os.path.join(root, f) for f in ('Erdos361.lean', 'Solution.lean', 'Challenge.lean', 'CheckOriginal.lean')]
pats = {
    'kernel/trust options': r'set_option\s+(debug\.\S+|trustCompiler|backward\.\S+|Elab\.\S+|compiler\.\S+)',
    'any set_option': r'set_option\s+\S+',
    'axiom/sorry/admit': r'\b(axiom|sorry|admit|sorryAx)\b',
    'native/reduceBool': r'native_decide|ofReduceBool|ofReduceNat|Lean\.trustCompiler',
    'unsafe/extern/implemented_by/opaque': r'\bunsafe\b|@\[\s*extern|implemented_by|\bopaque\b',
    'metaprogramming': r'\bimport\s+Lean\b|\brun_cmd\b|\brun_elab\b|\brun_meta\b|#eval|\belab\b|\bmacro\b|\bmacro_rules\b|\bsyntax\b|addDecl',
    'instances': r'\binstance\b|attribute\s*\[\s*(local\s+|scoped\s+)?instance',
    'notation/coercions': r'\bnotation\b|\binfix[lr]?\b|\bprefix\b|\bpostfix\b|@\[\s*coe|\bunif_hint\b|default_instance',
    'scoped/local': r'\bscoped\b|attribute\s*\[\s*local',
    'namespaces': r'^\s*namespace\s+\S+',
    'imports': r'^\s*import\s+\S+',
}
for f in files:
    lines = strip_comments(read(f)).split('\n')
    print('=== %s (%d non-blank code lines)' % (os.path.relpath(f, root), sum(1 for l in lines if l.strip())))
    for k, p in pats.items():
        hits = sorted(set(l.strip() for l in lines if re.search(p, l)))
        n = sum(1 for l in lines if re.search(p, l))
        if hits:
            print('   %-36s %3d  %s' % (k, n, ' | '.join(hits)[:300]))

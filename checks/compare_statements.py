"""Compare Challenge.lean with Erdos361/Statement.lean (definitions) and Solution.lean (statements).
Usage: python3 -I compare_statements.py <project root>"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from _common import strip_comments, read, norm

root = sys.argv[1] if len(sys.argv) > 1 else '.'
st = norm(strip_comments(read(os.path.join(root, 'Erdos361', 'Statement.lean'))))
ch = norm(strip_comments(read(os.path.join(root, 'Challenge.lean'))))
so = norm(strip_comments(read(os.path.join(root, 'Solution.lean'))))
END = 'end Erdos361.Statement'
blk = lambda s: s[s.index('namespace Erdos361.Statement'): s.index(END) + len(END)]
print('[1] header  Statement:', repr(st[:st.index('namespace')]), ' Challenge:', repr(ch[:ch.index('namespace')]))
print('[1] definitions block identical:', blk(st) == blk(ch), '| length', len(blk(st)))
thms = lambda s, tail: {m.group(1): m.group(2).strip() for m in re.finditer(r'theorem (\S+)(.*?)' + tail, s)}
cth, sth = thms(ch, r':= by sorry'), thms(so, r':= (?:_root_\.)')
print('[2] theorems  Challenge:', len(cth), ' Solution:', len(sth), ' same names and order:', list(cth) == list(sth))
ok_all = len(cth) == 11 and list(cth) == list(sth)
for k in cth:
    ok = cth[k] == sth.get(k); ok_all &= ok
    print('    %-28s identical: %s' % (k, ok))
print('[2] ALL 11 IDENTICAL:', ok_all)
rest = ch[ch.index(END) + len(END):]
print('[3] preamble  Challenge:', repr(rest[:rest.index('theorem')].strip()))
print('    preamble  Solution :', repr(so[:so.index('theorem')].strip()))
for m in re.finditer(r'theorem (\S+).*?:= (_root_\.\S+)', so):
    print('    %-28s <- %s' % (m.group(1), m.group(2)))
residue = re.sub(r'theorem \S+.*?:= _root_\.\S+(?: [^#]*?)?(?=theorem|end Erdos361\.Statement)', '', so)
print('[4] Solution outside the 11 theorems:', residue)

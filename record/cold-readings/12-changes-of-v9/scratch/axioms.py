# Grepy Cotejo: #print axioms outputs in the final check logs present; trust-base search in the sources
import os, re, sys, collections
d = sys.argv[1]; root = sys.argv[2]
fs = sorted(f for f in os.listdir(d) if re.fullmatch(r'checkC\d+[a-h]?\.log', f) or f == 'checkC31b.log')
fs = [f for f in fs if f != 'checkC31.log']
tot = collections.Counter(); per = {}; nolist = []; ends = collections.Counter(); other = []
for f in fs:
    t = open(os.path.join(d, f), encoding='utf-8', errors='replace').read()
    c = collections.Counter()
    for m in re.finditer(r"^'([^']+(?:'')?)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", t, re.M):
        key = m.group(3) if m.group(3) is not None else 'NONE'
        c[key] += 1
        if key == 'NONE': nolist.append((f, m.group(1)))
    per[f] = c; tot += c
    last = t.strip().split('\n')[-1]; ends[last.split(' pico')[0]] += 1
    if 'sorryAx' in t: other.append((f, 'sorryAx'))
print('final check logs present:', len(fs))
print('axiom lines total:', sum(tot.values()), dict(tot))
print('no-axiom lines:', nolist)
print('log endings:', dict(ends))
print('sorryAx:', other)
# names with fewer axioms
for f in fs:
    t = open(os.path.join(d, f)).read()
    for m in re.finditer(r"^'(.+)' depends on axioms: \[(propext, Quot.sound|propext)\]", t, re.M):
        print('  fewer:', f, m.group(1), m.group(2))
# trust base, comment-aware
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
def strip(s):
    out=[];i=0;n=len(s);dep=0
    while i<n:
        if dep==0 and s.startswith('--',i):
            j=s.find('\n',i); i=n if j<0 else j; continue
        if s.startswith('/-',i): dep+=1;i+=2;continue
        if dep>0 and s.startswith('-/',i): dep-=1;i+=2;continue
        if dep>0:
            i+=1;continue
        out.append(s[i]);i+=1
    return ''.join(out)
words = ['sorry','admit','native_decide','implemented_by','extern','unsafe','opaque','partial','axiom','decide']
cnt = collections.Counter(); filesw = collections.defaultdict(set); raw_axiom = 0
for dd, _, ff in os.walk(os.path.join(root, 'RequestProject')):
    for f in ff:
        if not f.endswith('.lean'): continue
        p = os.path.join(dd, f); s = open(p, encoding='utf-8').read(); c = strip(s)
        raw_axiom += len(re.findall(r'axiom', s, re.I))
        for w in words:
            k = len(re.findall(r'(?<![\w.])' + w + r'(?![\w])', c))
            if k: cnt[w] += k; filesw[w].add(p)
print('in code (comments stripped):', {w: (cnt[w], len(filesw[w])) for w in words})
print("substring 'axiom' anywhere (case-insensitive, comments included):", raw_axiom)

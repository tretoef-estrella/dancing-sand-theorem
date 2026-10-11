# Grepy Cotejo: count Lean files, lines, theorem/lemma declarations; and check the clean-rebuild log.
import os, re, sys, hashlib, collections
root = sys.argv[1]; rebuild = sys.argv[2]; manifest = sys.argv[3]
files = []
for d, _, fs in os.walk(os.path.join(root, 'RequestProject')):
    for f in fs:
        if f.endswith('.lean'): files.append(os.path.join(d, f))
files.sort()
print('lean files under RequestProject:', len(files))
main = [f for f in files if os.path.basename(f) == 'Main.lean' and os.path.dirname(f).endswith('RequestProject')]
print('Main.lean at top:', len(main))

def strip_comments(s):
    out = []; i = 0; n = len(s); depth = 0; instr = False
    while i < n:
        if depth == 0 and not instr and s.startswith('--', i):
            j = s.find('\n', i); j = n if j < 0 else j
            i = j; continue
        if not instr and s.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth > 0 and s.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth > 0:
            if s[i] == '\n': out.append('\n')
            i += 1; continue
        c = s[i]
        if c == '"' and (i == 0 or s[i-1] != '\\') and not (i > 0 and s[i-1] == "'"):
            instr = not instr
        out.append(c); i += 1
    return ''.join(out)

tot_lines = 0; tot_lines_nomain = 0; col0 = 0; decl = 0; attr = collections.Counter(); col0_in_comment = 0
mods = set()
decl_re = re.compile(r'^[ \t]*((?:@\[[^\]]*\][ \t]*\n?[ \t]*)*)((?:(?:private|protected|noncomputable|nonrec)[ \t]+)*)(theorem|lemma)\b', re.M)
for f in files:
    raw = open(f, encoding='utf-8').read()
    nl = raw.count('\n'); tot_lines += nl
    if f not in main: tot_lines_nomain += nl
    rel = os.path.relpath(f, root)[:-5].replace('/', '.'); mods.add(rel)
    # column-0 rule of the certificate (raw text)
    c0 = sum(1 for l in raw.split('\n') if l.startswith('theorem ') or l.startswith('lemma '))
    col0 += c0
    code = strip_comments(raw)
    c0code = sum(1 for l in code.split('\n') if l.startswith('theorem ') or l.startswith('lemma '))
    col0_in_comment += c0 - c0code
    for m in decl_re.finditer(code):
        decl += 1
        a = m.group(1).strip()
        if a:
            attr[re.sub(r'\s+', ' ', a)] += 1
print('lines (newline chars) all files:', tot_lines, ' without Main.lean:', tot_lines_nomain, ' Main.lean:', tot_lines - tot_lines_nomain)
print("column-0 rule lines ('theorem '/'lemma ' at col 0, raw):", col0, ' of which inside comments:', col0_in_comment)
print('theorem/lemma declarations in code (comments stripped, attributes allowed):', decl)
print('declarations preceded by an attribute:', sum(attr.values()), dict(attr))
# rebuild log
lines = open(rebuild).read().split('\n')
ents = [l for l in lines if l.startswith('RequestProject.')]
ok = [l for l in ents if 'VIGIA-FIN-OK exit=0' in l]
bm = set(l.split()[0] for l in ents)
print('rebuild entries:', len(ents), ' exit=0:', len(ok), ' distinct modules:', len(bm), ' equal to source modules:', bm == mods)
print('rebuild other lines:', [l for l in lines if l and not l.startswith('RequestProject.')])
# manifest of 416
man = [l.split() for l in open(manifest).read().strip().split('\n')]
bad = 0
for h, p in man:
    if hashlib.md5(open(os.path.join(root, p), 'rb').read()).hexdigest() != h: bad += 1
print('manifest lines:', len(man), ' bad md5:', bad, ' md5 of manifest file:', hashlib.md5(open(manifest,'rb').read()).hexdigest())

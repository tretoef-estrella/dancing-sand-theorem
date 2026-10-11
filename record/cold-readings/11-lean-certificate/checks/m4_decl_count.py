# M4: how many theorem/lemma declarations does the project have, counted in code only (comments removed),
# with any indentation, attributes and modifiers? Which ones does the certificate's column-0 rule miss?
import os, re, sys, collections
sys.path.insert(0, 'checks')
from m3_trustbase import code_mask
RP = 'material/project/RequestProject'
miss = collections.Counter(); total = col0 = 0; examples = []
for d, _, fs in os.walk(RP):
    for f in fs:
        if not f.endswith('.lean') or f == 'Main.lean': continue
        p = os.path.join(d, f); src = open(p, encoding='utf-8').read(); m = code_mask(src)
        off = 0
        for line in src.split('\n'):
            mo = re.match(r'(\s*)((?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec|noncomputable)\s+)*)(theorem|lemma)\s', line)
            if mo and m[off + mo.start(3)]:
                total += 1
                if line.startswith(('theorem ', 'lemma ')): col0 += 1
                else:
                    key = ('indented ' if mo.group(1) else '') + (mo.group(2).strip().split()[0] if mo.group(2).strip() else '')
                    miss[key] += 1
                    if len(examples) < 6: examples.append(os.path.relpath(p, RP) + ': ' + line.strip()[:90])
            off += len(line) + 1
print('theorem/lemma declarations in code (68 folders):', total, '; at column 0 (the certificate rule):', col0)
print('missed by the rule, by kind:', dict(miss)); print('examples:'); [print('  ', e) for e in examples]

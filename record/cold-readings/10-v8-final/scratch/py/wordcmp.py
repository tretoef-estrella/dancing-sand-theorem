# Word comparison of pdftotext of the v7 and v8 pdfs, page numbers removed. Prints every differing run with context.
import re, sys, subprocess, difflib
def words(pdf, dmg=None):
    t = subprocess.run(['pdftotext', '-layout', pdf, '-'], capture_output=True, text=True).stdout
    pages = t.split('\f')
    out = []
    for n, p in enumerate(pages, 1):
        lines = p.split('\n')
        # the folio: a line that holds only the page number (pages 2..N)
        keep = [l for l in lines if not re.fullmatch(r'\s*' + str(n) + r'\s*', l)]
        for l in keep:
            for w in l.split():
                out.append((w, n))
    if dmg: out = dmg(out)
    return out
a = words(sys.argv[1]); 
dmg = None
if len(sys.argv) > 3 and sys.argv[3] == 'control':
    # control: drop one word of §7 and change one digit of §12 in the v8 text; both must show up as extra differences
    def dmg(o):
        o = list(o); i = [k for k, (w, n) in enumerate(o) if w == 'antitonic'][0]; del o[i]
        j = [k for k, (w, n) in enumerate(o) if w == '192'][-1]; o[j] = ('193', o[j][1]); return o
b = words(sys.argv[2], dmg)
aw, bw = [w for w, _ in a], [w for w, _ in b]
print(f'words: v7 {len(aw)}, v8 {len(bw)}')
sm = difflib.SequenceMatcher(None, aw, bw, autojunk=False)
ops = [o for o in sm.get_opcodes() if o[0] != 'equal']
print(f'differing runs: {len(ops)}')
for op, a1, a2, b1, b2 in ops:
    pa = a[a1][1] if a1 < len(a) else a[-1][1]; pb = b[b1][1] if b1 < len(b) else b[-1][1]
    print(f'--- {op} v7 p.{pa} words {a1}-{a2} ({a2-a1}) | v8 p.{pb} words {b1}-{b2} ({b2-b1})')
    print('   v7: ' + ' '.join(aw[max(0,a1-6):a1]) + ' [[ ' + ' '.join(aw[a1:a2]) + ' ]] ' + ' '.join(aw[a2:a2+6]))
    print('   v8: ' + ' '.join(bw[max(0,b1-6):b1]) + ' [[ ' + ' '.join(bw[b1:b2]) + ' ]] ' + ' '.join(bw[b2:b2+6]))

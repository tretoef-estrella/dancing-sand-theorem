# Each line added by the diff v7->v8 must appear, word for word and in order, in the pdftotext of the v8 pdf
# (md markup removed; pdf line-end hyphens rejoined). Control: the same on the v7 pdf must miss the new lines.
import re, sys, subprocess
pdf = sys.argv[1]
t = subprocess.run(['pdftotext', pdf, '-'], capture_output=True, text=True).stdout
t = re.sub(r'\n\s*\d+\s*\n', '\n', t)            # folios
t = re.sub(r'(\w)[‐-]\s*\n\s*(\w)', r'\1\2', t)    # line-end hyphens (U+2010 or -)
T = ' ' + re.sub(r'\s+', ' ', t) + ' '
def norm(s):
    s = s.lstrip('+').strip()
    s = re.sub(r'^- ', '', s); s = s.replace('**', '').replace('`', '')
    return re.sub(r'\s+', ' ', s).strip()
added = [l for l in open('material/paper/DIFF_v7_to_v8.txt', encoding='utf-8').read().split('\n') if l.startswith('+') and not l.startswith('+++') and l[1:].strip()]
miss = 0
for l in added:
    s = norm(l)
    # split into sentences-ish pieces at '. ' so a page turn or a table between pieces does not hide a match
    for piece in [p for p in re.split(r'(?<=[.;:])\s', s) if len(p) > 3]:
        ok = (' ' + piece + ' ') in T or piece in T
        if not ok:
            miss += 1; print('MISS:', piece[:160])
print(f'added lines: {len(added)}; pieces missed: {miss}')

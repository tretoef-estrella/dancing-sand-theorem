# -*- coding: utf-8 -*-  (added 11 Oct 2026: without it this Python misreads the very long FORCECODE line)
# cert_md2html.py (HYPERCUBE, 11 Oct 2026): copy of corpus4/herramientas_grepy/regla318_cert_md2html.py (the builder of the Chaise Lean certificate v2), used unchanged for the cube.
# regla316_cert_md2html.py (4 Oct 2026): copy of regla290 with three more Lean-identifier shapes printed as code:
# R4, S5a, Q'1, A0–A4 (letter+digit), D2_DJ (letters+digits_word), theorem_i/ii/iii (lowercase word_...).
# regla290_cert_md2html.py (30 Sep 2026): copy of regla289 with the title taken from argv[3]. Usage: IN.md OUT.html "Title"
# identifiers with two underscores (SAT_le_K), lowercase_X (finrank_K) and X_lower (V_free); tables may break across pages.
# regla287_cert_md2html.py — copy of regla277_md2html.py for the Lean certificate (29 Sep 2026):
# adds fenced code blocks (```) as <pre>, Lean identifiers in inline code as monospace, and no nowrap columns.
# regla277_md2html.py — copy of regla272_md2html.py with footnotes, for PAPER_OFICIAL_v4 (Grepy el Auditor, 2026-09-25).
# Footnotes: inline [^n] -> superscript; a line '[^n]: text' -> a small note printed right after the paragraph.
# No external packages. Handles: headings, paragraphs, bold/italic, inline code (rendered as math, with
# ^{..}/_{..} turned into sup/sub), display formulas (a line that is only code), nested lists, blockquotes,
# tables, horizontal rules. Usage: python3 regla272_md2html.py IN.md OUT.html
# 11 Oct 2026, after the cold reading: added '[propext]', 'lemma_0b', 'lemma_0d', 'lemma_0e' (printed as math in the first build too), 'wf_simp', 'wf_close', 'lV', 'lP', 'theorem', 'lemma', 'lean/…', 'logs/…', 'checks/…'.
# FORCED AS CODE (11 Oct 2026, HYPERCUBE): inline code spans in this exact list are Lean names or Lean expressions of the cube's certificate.
FORCECODE = {'[propext]','lemma_0b','lemma_0d','lemma_0e','wf_simp','wf_close','lV','lP','theorem','lemma','lean/…','logs/…','checks/…','G n','Ids','Sylp','XFam λ ((n − λ)/2)','s2','v2','G','e','K','h','m','Q','lap','coker','aElt','mk','minOr','bit','dancer','next','M3_support','e i = Pi.single i 1','G n = Fin n → ZMod 2','lap ℤ n f g = n·f g − Σ_i f (g + e i)','CubeLaplacian.L n = lap ℤ n','dancer I p','levelSet N z j','yPool ds i','yPool0 ds','cokerBar n ≃ ℤ × KBar n','KBar n','coker n','l0 S = \\|S/2S\\|','l1 S = \\|2S/4S\\|','cExp S r','layer S (e−1)','layer S j = \\|2^j S / 2^{j+1} S\\|','lam k I = 2^k + oE I − 1','m λ n','L (n+1) = (L n).flatMap Vdot','S % P','aElt n = 𝟙','Gbar n','lapBar ℤ n u x = n·u x − Σ_i u (x + mk (e i))','Nat.digits 2 x','v2 = padicValNat 2','toNat','≃+', 'I = Ids (ds λ)', '.lake/build', 'twoM', 'oE', 'ds', 'DW', 'blockF', 'ℤ_[2]', 'C109', 'gmax N', 'Main', 'Fold', 'IsFit', 'toNat', 'lemma_P1_*', 'xi', 'XFam', '.lake/packages', 'coker', 'lean-toolchain', 'corollary_A1', 'Bf A', '.All', 'M3_*', 'ifit', 'KBar_finite', 'Filt', 'TT', 'lemma_0f', 'g + e i', 'lapBar', 'RA R', 'm λ n = (L n).count λ', 'r < S % P', 'SC', 'fit N x', 'dancer I 0 = ∅', 'layer', 'theorem ', 'k = (ds λ).length', 'fit', 'aN', '.olean', 'm λ n = 0', 'ds (2l+2) = true :: ds l', 'Sylp p T = {y \\| ∃ k, p^k • y = 0}', 'yPool', 'abbrev', 'lap ℤ n', 'h k I t = next k I t − t', 'lap ℤ n f g = n·f g − Σ_i f (g + e i)', 'm λ n', '[n, n] ++ (Vdot (n/2)).map (2·+1)', 'DPLattice', '⋯.choose', 'true', 'corollary_A2', 'lemma_A1', 'yPool0', 'phi', 'noncomputable abbrev', 'ℚ_[2]', 'next', 'Bend', 'Lc', 'ds λ', 'ds 0 = []', 'Vdot', 'Q', 's2 x', 'L n', 'lemma_0a', 'lam', 'rfl', 'def', 'RS', 'K n', 'sqDist', 'clock', 'hSum', 'KBar n', "M1'", 'match', 'corollary_B1', 'KBar', 'l0', 'La', 'l0 H = l1 H', 'dancer I p = {t ∈ I \\| bit_{rank t}(p) = 1}', 'L 0 = [0]', 'Gbar', 'Vdot 0 = [1]', 'dd_top', 'Vdot (n+1) = [n+2]', 'lemma_P4', 'lemma ', 'l1', 'clock k I i D', 'coker n ≃ ℤ × K n', 'lemma_P2', 'gmax', 'NonIncr', "DW'", 'lemma_B1', 'S % P', 'cExp', 'ds (2l+1) = false :: ds l', 'M1_*', 'kappa', 'noncomputable def', 'levelSet'}
import sys, re, html

def mathify(s):
    # s: raw code-span content (unescaped). Convert ^{..}, _{..}, ^c, _c into sup/sub, recursively.
    out = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c in '^_' and i + 1 < n and i > 0:
            tag = 'sup' if c == '^' else 'sub'
            if s[i+1] == '{':
                depth, j = 0, i + 1
                while j < n:
                    if s[j] == '{': depth += 1
                    elif s[j] == '}':
                        depth -= 1
                        if depth == 0: break
                    j += 1
                inner = s[i+2:j]
                out.append(f'<{tag}>{mathify(inner)}</{tag}>')
                i = j + 1
                continue
            else:
                ch = s[i+1]
                # keep combining marks with their base character
                k = i + 2
                while k < n and 0x0300 <= ord(s[k]) <= 0x036F: k += 1
                out.append(f'<{tag}>' + html.escape(s[i+1:k]).replace('*', '&#42;') + f'</{tag}>')
                i = k
                continue
        out.append(html.escape(c).replace('*', '&#42;'))
        i += 1
    return ''.join(out)

LEANLIKE = re.compile(r"^[A-Z]'?\d{1,2}[a-z]?(–[A-Z]'?\d{1,2}[a-z]?)?$|^(Qk|Qall|RZ) |^[A-Za-z]+\d+_\w+$|^[a-z]{4,}_[a-z/]+$|^#|^lake |[A-Z]{3,}_[A-Z]{3,}|^[a-z]+/$|[A-Za-z0-9]+_[A-Za-z0-9]+_[A-Za-z0-9]|[a-z]{5,}_[A-Z]\b|\b[A-Z]_[a-z]{3,}|[A-Za-z]{2,}\d|\d_[a-z]|[a-z][A-Z]|[A-Za-z]\.[A-Za-z]|[a-z]{3,}_[A-Z]{2}|[a-z]{3,}_[a-z]{2,}|_[A-Z][a-z]|\b[A-Z][a-z]{4,}\b|^(sorry|admit|axiom|decide|native_decide|propext|unsafe|opaque|lake|grep|implemented_by|partial def|pp\.\*)$|\bFin\b|:=|@\[|^[0-9a-f]{8}|\d\.\d+\.\d")
def code_html(content):
    content = content.replace('\\|', '|')
    if content in FORCECODE or re.search(r'\.(py|log|md|txt|cpp|m2|lean|gz)\b', content) or LEANLIKE.search(content):
        return '<code class="file">' + html.escape(content).replace('*', '&#42;') + '</code>'
    return f'<span class="m">{mathify(content)}</span>'

def inline(s):
    parts = re.split(r'(`[^`]*`)', s)
    res = []
    for p in parts:
        if p.startswith('`') and p.endswith('`') and len(p) >= 2:
            res.append(code_html(p[1:-1]))
        else:
            t = html.escape(p.replace('\\|', '|'), quote=False)
            t = re.sub(r'\[\^(\w+)\]', r'<sup class="fnref">\1</sup>', t)
            t = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', t)
            t = re.sub(r'(?<![\w*])\*(?!\s)(.+?)(?<!\s)\*(?![\w*])', r'<em>\1</em>', t)
            res.append(t)
    out = ''.join(res)
    # bold/italic spanning code spans: second pass on the assembled string outside tags is risky; handle **..** across spans
    out = re.sub(r'\*\*(.+?)\*\*', r'<strong>\1</strong>', out)
    out = re.sub(r'(?<![\w*>])\*(?!\s)([^*]+?)(?<!\s)\*(?![\w*])', r'<em>\1</em>', out)
    return out

def is_display(line):
    s = line.strip()
    if not s.startswith('`'): return False
    rest = re.sub(r'`[^`]*`', '', s)
    return (re.fullmatch(r'[\s,.;:()0-9]*', rest) is not None or re.fullmatch(r'[\s,.;:]*\([^()]*\)[\s.∎]*', rest) is not None) and s.count('`') >= 2

def split_row(line):
    line = line.strip()
    if line.startswith('|'): line = line[1:]
    if line.endswith('|'): line = line[:-1]
    cells, cur, incode = [], '', False
    for ch in line:
        if ch == '`': incode = not incode
        if ch == '|' and not incode:
            cells.append(cur); cur = ''
        else:
            cur += ch
    cells.append(cur)
    return [c.strip() for c in cells]

def convert(md):
    lines = md.split('\n')
    out = []
    i = 0
    first_h1 = True
    after_h1 = False
    para = []
    front = [True]
    def flush_para():
        nonlocal para
        if para:
            cls = ' class="front"' if front[0] else ''
            out.append(f'<p{cls}>' + ' '.join(inline(x) for x in para) + '</p>')
            para = []
    while i < len(lines):
        line = lines[i]
        s = line.strip()
        if s.startswith('```'):
            flush_para(); i += 1; buf = []
            while i < len(lines) and not lines[i].strip().startswith('```'):
                buf.append(lines[i]); i += 1
            i += 1
            out.append('<pre class="lean">' + html.escape('\n'.join(buf)) + '</pre>')
            continue
        if not s:
            flush_para(); i += 1; continue
        fm = re.match(r'^\[\^(\w+)\]:\s*(.*)$', s)
        if fm:
            flush_para()
            out.append(f'<div class="fn"><sup>{fm.group(1)}</sup>&#8201;' + inline(fm.group(2)) + '</div>')
            i += 1; continue
        if s == '---':
            flush_para(); out.append('<hr/>'); front[0] = False; i += 1; continue
        m = re.match(r'^(#{1,4})\s+(.*)$', s)
        if m:
            flush_para()
            lvl = len(m.group(1)); txt = inline(m.group(2))
            if lvl == 1 and first_h1:
                out.append(f'<h1 class="title">{txt}</h1>'); first_h1 = False; after_h1 = True
            elif lvl == 2 and after_h1:
                out.append(f'<h2 class="subtitle">{txt}</h2>'); after_h1 = False
            else:
                out.append(f'<h{lvl}>{txt}</h{lvl}>'); after_h1 = False
            i += 1; continue
        after_h1 = False
        if s.startswith('|') and i + 1 < len(lines) and re.match(r'^\|?\s*:?-{3,}', lines[i+1].strip()):
            flush_para()
            head = split_row(s); i += 2
            rows = []
            while i < len(lines) and lines[i].strip().startswith('|'):
                rows.append(split_row(lines[i])); i += 1
            h = '<table><thead><tr>' + ''.join(f'<th>{inline(c)}</th>' for c in head) + '</tr></thead><tbody>'
            for r in rows:
                h += '<tr>' + ''.join(f'<td>{inline(c)}</td>' for c in r) + '</tr>'
            out.append(h + '</tbody></table>')
            continue
        if s.startswith('>'):
            flush_para()
            buf = []
            while i < len(lines) and lines[i].strip().startswith('>'):
                buf.append(lines[i].strip()[1:].strip()); i += 1
            parts, cur, items = [], [], []
            for x in buf:
                if x.startswith('- '):
                    if cur: parts.append('<p>' + ' '.join(inline(y) for y in cur) + '</p>'); cur = []
                    items.append(inline(x[2:]))
                else:
                    if items: parts.append('<ul>' + ''.join(f'<li>{t}</li>' for t in items) + '</ul>'); items = []
                    if x and is_display(x):
                        if cur: parts.append('<p>' + ' '.join(inline(y) for y in cur) + '</p>'); cur = []
                        parts.append('<div class="display">' + inline(x) + '</div>')
                    elif x: cur.append(x)
                    elif cur: parts.append('<p>' + ' '.join(inline(y) for y in cur) + '</p>'); cur = []
            if cur: parts.append('<p>' + ' '.join(inline(y) for y in cur) + '</p>')
            if items: parts.append('<ul>' + ''.join(f'<li>{t}</li>' for t in items) + '</ul>')
            out.append('<blockquote>' + ''.join(parts) + '</blockquote>')
            continue
        lm = re.match(r'^(\s*)([-*]|\d+\.)\s+(.*)$', line)
        if lm:
            flush_para()
            # collect list block
            items = []  # (indent, ordered, text)
            while i < len(lines):
                l = lines[i]
                mm = re.match(r'^(\s*)([-*]|\d+\.)\s+(.*)$', l)
                if mm:
                    items.append([len(mm.group(1)), mm.group(2)[0].isdigit(), mm.group(3)]); i += 1
                elif l.strip() and l.startswith(' ') and items:
                    items[-1][2] += ' ' + l.strip(); i += 1
                else:
                    break
            out.append(render_list(items))
            continue
        if is_display(line):
            flush_para()
            out.append('<div class="display">' + inline(s) + '</div>')
            i += 1; continue
        para.append(s); i += 1
    flush_para()
    return '\n'.join(out)

def render_list(items):
    html_out = []
    stack = []  # (indent, tag)
    for ind, ordered, text in items:
        tag = 'ol' if ordered else 'ul'
        while stack and ind < stack[-1][0]:
            html_out.append(f'</li></{stack[-1][1]}>'); stack.pop()
        if not stack or ind > stack[-1][0]:
            html_out.append(f'<{tag}>'); stack.append((ind, tag))
        else:
            html_out.append('</li>')
        html_out.append('<li>' + inline(text))
    while stack:
        html_out.append(f'</li></{stack[-1][1]}>'); stack.pop()
    return ''.join(html_out)

CSS = r'''
@page { size: A4; margin: 20mm 19mm 20mm 19mm; }
html { -webkit-print-color-adjust: exact; }
body { font-family: "STIX Two Text", "STIXGeneral", "Times New Roman", serif; font-size: 10.6pt; line-height: 1.46;
       color: #111; max-width: 172mm; margin: 0 auto; text-align: justify; hyphens: auto; }
h1.title { font-size: 25pt; text-align: center; letter-spacing: 0.06em; margin: 4mm 0 2mm 0; font-weight: 700; }
h2.subtitle { font-size: 13.5pt; text-align: center; font-weight: 400; font-style: italic; margin: 0 0 6mm 0; border: none; }
h2 { font-size: 14pt; margin: 7mm 0 2.5mm 0; padding-bottom: 1mm; border-bottom: 0.4pt solid #888; page-break-after: avoid; }
h3 { font-size: 11.6pt; margin: 4.5mm 0 1.5mm 0; page-break-after: avoid; }
h4 { font-size: 10.8pt; margin: 3mm 0 1mm 0; }
p { margin: 1.6mm 0; }
p.front { text-align: center; margin: 1.2mm 6mm; }
.m { font-family: "STIX Two Text", "STIX Two Math", "STIXGeneral", serif; font-style: italic; white-space: normal; }
em .m, blockquote em .m { font-style: normal; }
.m sub, .m sup { font-size: 72%; line-height: 0; }
code.file { font-family: "Menlo", monospace; font-size: 8.6pt; color: #333; }
.display { text-align: center; margin: 2.2mm 0; }
blockquote { margin: 3mm 4mm; padding: 2.5mm 4mm; border-left: 2.5pt solid #444; background: #f4f4f4; }
blockquote p { margin: 1mm 0; }
blockquote ul { margin: 0.8mm 0 0.8mm 2mm; }
.display .m { font-style: italic; }
ul, ol { margin: 1.2mm 0 1.2mm 6mm; padding-left: 4mm; }
li { margin: 0.6mm 0; }
table { border-collapse: collapse; margin: 3mm auto; font-size: 9.2pt; page-break-inside: avoid; }
th, td { border: 0.4pt solid #999; padding: 1.2mm 2mm; text-align: center; vertical-align: top; }
th { background: #eee; }
pre.lean { font-family: 'Menlo', monospace; font-size: 7.6pt; line-height: 1.32; background: #f6f6f6; border: 0.4pt solid #ccc; padding: 2mm 3mm; white-space: pre-wrap; word-break: break-word; text-align: left; page-break-inside: avoid; }
table { font-size: 8.4pt; }
td { text-align: left; }
hr { border: none; border-top: 0.4pt solid #aaa; margin: 5mm 0; }
strong { font-weight: 700; }
sup.fnref { font-size: 70%; line-height: 0; }
.fn { font-size: 8.4pt; line-height: 1.35; margin: 1.4mm 0 2.4mm 0; text-align: justify; color: #222; }
.fn::before { content: ""; display: block; width: 32%; border-top: 0.4pt solid #999; margin-bottom: 0.9mm; }
.fn sup { font-size: 75%; }
table { page-break-inside: auto; } tr { page-break-inside: avoid; }
td code.file { word-break: normal; overflow-wrap: normal; white-space: nowrap; }  /* HYPERCUBE 11 Oct: a Lean name in a table is never cut */

code, code.file, .m, pre.lean { hyphens: manual; -webkit-hyphens: manual; page-break-inside: auto; break-inside: auto; }
code.file { overflow-wrap: anywhere; }
p:has(+ table) { break-after: avoid; page-break-after: avoid; }  /* 11 Oct, cold reading 11 P-D1: a caption stays with its table */
'''

if __name__ == '__main__':
    md = open(sys.argv[1], encoding='utf-8').read()
    body = convert(md)
    doc = ('<!DOCTYPE html><html lang="en"><head><meta charset="utf-8"><title>' + html.escape(sys.argv[3]) + '</title>'
           f'<style>{CSS}</style></head><body>\n{body}\n</body></html>')
    open(sys.argv[2], 'w', encoding='utf-8').write(doc)
    print('ok', len(doc))

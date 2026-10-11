# Grepy Cotejo: which pages of the certificate pdf carry text changed by the corrections
import subprocess, re
t = subprocess.run(['pdftotext', '-layout', 'material/evidence/certificate/LEAN_CERTIFICATE_DANCING_SAND_v1.pdf', '-'], capture_output=True, text=True).stdout
pages = t.split('\f')
print('pages', len([p for p in pages if p.strip()]))
keys = {'header «read cold and corrected»': 'read cold and corrected the same day',
 '§0 DW n≥2': 'and, for n ≥ 2, its equivalent form', '§0 Thm 4.1 n≥3': 'Theorem 4.1 for n ≥ 3', '§0 Read cold': 'Read cold. A reader other',
 '§1.1 Twenty-four': 'Twenty-four statements are printed here', '§1.3 folded row': 'Version 8 of the paper describes the edges',
 '§1.3 DW row n=1': 'Lean does not state that case', '§1.3 Cor 1.6 row': 'the case n = 2 (K(Q', 'Generality': 'In Corollary 1.6, Gao et',
 '§1.4': 'twenty-one statements of §1.1 named there', '§2 item 7': 'The cold reading. On 11 October', '§3 bold sentence': 'The names in bold are statements printed',
 '§3.3 watchdog': "except the watchdog's final line", '§4 attribute': 'attribute [instance] DPLattice.fintype', '§4 885': '885 lines of', '§4 §1.4': 'statements of §1.4 give the three',
 '§6 checks rule': 'where the log reports counts by kind only', '§6 lines column': 'the declarations are counted in §7', '§6 two tables': 'Two columns of Table 6a were transcribed',
 'Table 6a C1': '1 591 122 checks in 10 kinds', 'Table 6a C52': '204 checks, 0 failures', 'Table 6b header': 'Peak GiB', '§7 3 449': 'Theorem and lemma declarations in code: 3 449',
 '§8 Paths': 'Every path in this certificate is relative', '§8 identical': 'final line (time and memory). CertCubo'}
def norm(s): return re.sub(r'\s+', ' ', s.replace('‑', '-').replace('’', "'"))
for k, v in keys.items():
    hits = [i + 1 for i, p in enumerate(pages) if norm(v) in norm(p)]
    print(f'{k}: pages {hits}')

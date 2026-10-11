# paths_v2.py — Grepy Escribano, 11 Oct 2026. Moves every path cited in LEAN_CERTIFICATE_DANCING_SAND_v2.src.md from
# the author's working tree (flat lean/ and logs/) to the published layout of the Lean record, version 2 (Rafa's
# order: lean/ and logs/ hold a README and folders only), and rewrites the «Paths» paragraph of §8 to say so.
# Run after cold_fixes_REMATE.py, before fill_v2.py. With an argument (the staged package folder) it also checks
# that every concrete path cited exists there. No other word changes.
import os, re, sys
H = os.path.dirname(os.path.abspath(__file__)); F = os.path.join(H, 'LEAN_CERTIFICATE_DANCING_SAND_v2.src.md')
s = open(F, encoding='utf-8').read()
assert 'PATHS_WORKING_TREE_TO_PUBLISHED' not in s, 'already applied'
OLD = "**Paths.** Every path in this certificate is relative to the project folder of the author's working tree; the public repository keeps the same relative paths (`lean/…`, `logs/…`, `checks/…`)."
NEW = ("**Paths.** Every path in this certificate is relative to the published folder of the Lean record; the Zenodo record "
       "and the public repository have the same layout. `lean/` holds the certificate (`CERTIFICADO/`), the project "
       "(`proyecto_cubo/`), the clean rebuild (`clean_rebuild/`), the pieces (`pieces/`), the brute-force scripts "
       "(`brute_force/`), the build scripts (`build/`) and the audit log (`audit/`); `logs/` holds the logs of the "
       "brute-force checks (`brute_force/`), of the builds (`build/`), of the check files of the pieces (`piece_checks/`) "
       "and of the final checks (`final_checks/`); `checks/…` is inside `lean/proyecto_cubo/`. The author's working tree "
       "keeps the files of those subfolders directly in `lean/` and `logs/`, and the scripts and logs use those names; "
       "`lean/PATHS_WORKING_TREE_TO_PUBLISHED.tsv` maps every name. The changes of version 2 were read cold with the paths "
       "of the working tree; the paths were then moved to this layout by `lean/CERTIFICADO/paths_v2.py`, which checks that "
       "every path cited exists in the published folder, and no other word changed.")
assert s.count(OLD) == 1; s = s.replace(OLD, '\x00PATHS\x00')

def pub(d, f):
    if d == 'lean':
        if re.match(r'C(\d+[a-h]?_.*|\*)\.md$|instrC.*\.txt$|msgC.*\.txt$', f): return 'lean/pieces/' + f
        if re.match(r'chkC.*\.py$|chkC.*_estimate\.txt$|chk_lattice_lib\.py$', f): return 'lean/brute_force/' + f
        if re.match(r'buildC.*\.(sh|txt)$', f): return 'lean/build/' + f
        if f == 'INFORME_ARISTOTLE_CUBO_v1.md': return 'lean/audit/' + f
    if d == 'logs':
        if f.startswith('chkC'): return 'logs/brute_force/' + f
        if f.startswith('buildC'): return 'logs/build/' + f
        if re.match(r'(checkC|CheckC)(\d|<N>)', f): return 'logs/piece_checks/' + f
        if re.match(r'(CheckCubo|CertCubo|DepsCubo)', f): return 'logs/final_checks/' + f
    return None

cited, moved = [], []
def rep(m):
    d, rest = m.group(1), m.group(2)
    if '/' in rest:                    # a path inside a subfolder (CERTIFICADO/, clean_rebuild/, proyecto_cubo/): unchanged
        cited.append(d + '/' + rest); return m.group(0)
    new = pub(d, rest)
    if new is None: raise SystemExit('no published place for ' + d + '/' + rest)
    cited.append(new); moved.append((d + '/' + rest, new)); return new
s = re.sub(r'(?<![\w/])(lean|logs)/([A-Za-z0-9_<>*.()+-]+(?:/[A-Za-z0-9_<>*.()+-]*)*)', rep, s)
s = s.replace('\x00PATHS\x00', NEW)
for a, b in moved: print('moved', a, '->', b)
if len(sys.argv) > 1:
    PKG = sys.argv[1]; bad = []
    for c in cited:
        if any(ch in c for ch in '<*'): continue          # patterns (C*.md, chkC<N>.py) are checked by their folder
        if not os.path.exists(os.path.join(PKG, c.rstrip('/'))): bad.append(c)
    for c in cited:
        if any(ch in c for ch in '<*'):
            if not os.path.isdir(os.path.join(PKG, os.path.dirname(c))): bad.append(c)
    assert not bad, ('missing in package', bad)
    print('every cited path exists in the package:', len(cited))
open(F, 'w', encoding='utf-8').write(s); print('written', F)

# make_tables_v2.py — Grepy Escribano, 11 Oct 2026 (version 2 of the certificate: make_tables.py plus piece C53;
# data in data_v2/, output data_v2/tables.md; the brute-force log of C53 reports PASS/FAIL lines, read below).
# make_tables.py — Grepy Escribano, 11 Oct 2026.
# Builds the per-piece tables of the Lean certificate of «The Dancing Sand Theorem» from data files,
# reading its numbers from data files (except the row of Main.lean, written below). Inputs (all in data/):
#   folders_counts.txt        «C-file folder files lines theorems defs» (source counts, Main.lean excluded)
#   clean_build_by_folder.txt «folder modules seconds peakGiB» (from the clean rebuild of 10-11 Oct)
#   tarballs_downloads.txt    «n md5 date time» of the Aristotle tarballs in ~/Downloads
# Output: data/tables.md
# and the brute-force logs logs/chkC<p>.log (number of checks and failures; read by checks_from_log below).
# 11 Oct 2026, after the cold reading of «Grepy Lacre» (F-ERR-1, F-PRES-4): the number of checks is no longer
# typed; it is read from each log. BF keeps only the controls (fired, total), transcribed by hand from the logs
# and checked against the 68 logs by the cold reader; its first entry is no longer used.
import os, re, ast
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data_v2')
LOGS = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'logs')

def checks_from_log(p):
    """(total, kinds) read from logs/chkC<p>.log; kinds = None when the log reports a total."""
    t = open(os.path.join(LOGS, f'chkC{p}.log'), encoding='utf-8').read().splitlines()
    assert t[-1].startswith('VIGIA-FIN-OK exit=0'), (p, t[-1])
    if p == '53':   # C53: one line «PASS …» per check, «FAIL CONTROL …» per control; no other FAIL line
        assert not any(l.startswith('FAIL') and not l.startswith('FAIL CONTROL') for l in t), p
        return sum(1 for l in t if l.startswith('PASS ')), None
    assert any(re.search(r'(FAILURES:? 0\b|failures 0\b|fails 0\b|\b0 failures)', l) for l in t), p
    total = None; kinds = {}
    for l in t:
        m = (re.search(r'(?:^|\b)(?:checks|CHECKS)[ :]+(\d+)', l) or re.search(r'(\d+) checks, \d+ failures', l)
             or re.search(r'TOTAL (\d+) FAILURES', l))
        if m: total = int(m.group(1))
        if l.startswith('COUNTS '): kinds = ast.literal_eval(l[7:])
        m = re.match(r'^checked (.+): (\d+)$', l)          # C1-C3
        if m: kinds[m.group(1)] = int(m.group(2))
        m = re.match(r'^([A-D]): (\d+) ', l)               # C4
        if m: kinds[m.group(1)] = int(m.group(2))
    if total is not None: return total, None
    assert kinds, p
    return sum(kinds.values()), len(kinds)

PIECES = ['1','2','3','4','5','6','7','8','9','10','11','12','13','14','15','16','17','18','19','20',
          '21','22','23','24','25','26','27','28','29','30','31','32','33','34','35','35b','36','37',
          '38','38b','39','39b','40','40b','40c','40d','41','42','43','44','45','46','47','48','48b',
          '49','49b','49c','50','50b','50c','50d','50e','50f','50g','50h','51','52','53']
# tarball number per piece (from the audit log; C1 has no number; (33) is a second download of (32))
TAR = {p: i for i, p in enumerate(PIECES[:33])}          # C1..C33 -> 0..32
for j, p in enumerate(PIECES[33:]): TAR[p] = 34 + j        # C34.. -> 34..
# Aristotle task per piece (from the audit log); C1 is recorded by its run id
TASK = dict(x.split() for x in """1 2b8cfa39
2 e0b97d3b
3 b15574a9
4 339a7b11
5 83be8821
6 194e2f27
7 a15e0203
8 13a49f40
9 813c96e8
10 0855be32
11 ad645d58
12 3f8eef5f
13 8906e033
14 a49f4cd1
15 6c933352
16 8cfae8e6
17 544ce1db
18 a46e4881
19 3209f52c
20 a60cc4f4
21 8d8b879c
22 3f5c9bd7
23 4cd90d1b
24 7a4cf945
25 aec9cbab
26 4b5ee80c
27 51e14db3
28 848f2784
29 c29eb434
30 dbbc5c96
31 148c191c
32 7a8f97ec
33 960dc443
34 2456f22c
35 4f36edd7
35b ffecadc3
36 bf28bdd8
37 dbf16242
38 5fde1d99
38b 02a121a5
39 f1cf204b
39b 579e5944
40 0246c6df
40b afeddeb6
40c 84a3b2d3
40d 23cdce92
41 86ac37fe
42 d4e089ce
43 198fbc5c
44 2cccc89d
45 76de0979
46 d36e2d4f
47 19843fc1
48 556eee6a
48b a5c4d914
49 1810c6c2
49b c6cd8d5a
49c 8ef876e1
50 ec5fa07e
50b 753368cf
50c 2759b7d5
50d 3af52ebd
50e 27ec0578
50f d6aa1d91
50g e5577a86
50h 3b91d694
51 222eb7ce
52 505f1414
53 dad27c9e""".splitlines())
# brute force before sending: (number of checks reported by the log or None, controls firing, controls)
BF = {'1':(None,2,2),'2':(None,5,5),'3':(None,3,3),'4':(None,4,4),'5':(None,3,3),'6':(None,4,4),
 '7':(None,3,3),'8':(None,5,5),'9':(None,4,4),'10':(None,5,5),'11':(None,4,4),'12':(None,5,5),
 '13':(144,4,4),'14':(None,5,5),'15':(None,3,3),'16':(None,4,4),'17':(7449,5,5),'18':(227,5,5),
 '19':(1030,5,5),'20':(2238,4,4),'21':(None,6,6),'22':(None,5,5),'23':(None,5,5),'24':(None,5,5),
 '25':(None,5,5),'26':(None,5,5),'27':(None,4,4),'28':(None,2,3),'29':(None,3,3),'30':(None,3,3),
 '31':(833,3,3),'32':(2343,3,3),'33':(2407,3,4),'34':(53945,4,4),'35':(337528,4,4),'35b':(22447,4,4),
 '36':(267891,5,5),'37':(83102,6,6),'38':(977,3,3),'38b':(254,4,4),'39':(711,4,4),'39b':(673,4,4),
 '40':(773,6,6),'40b':(412,6,6),'40c':(184,6,6),'40d':(493,5,5),'41':(334,5,5),'42':(528,5,5),
 '43':(19713,4,4),'44':(11994,5,5),'45':(1391,4,4),'46':(1008,4,4),'47':(12622,4,4),'48':(24493,5,5),
 '48b':(1286,3,3),'49':(288,4,4),'49b':(1464,3,4),'49c':(2437,5,5),'50':(4114,4,4),'50b':(11616,3,3),
 '50c':(10968,4,4),'50d':(35887,4,4),'50e':(8253,6,6),'50f':(750,4,4),'50g':(1490,4,4),'50h':(302,3,3),
 '51':(66,3,3),'52':(204,3,3),'53':(14,4,4)}

fold = {}
for line in open(os.path.join(D, 'folders_counts.txt')):
    c, f, nf, nl, nt, nd = line.split()
    p = re.match(r'C([0-9]+[a-h]?)_', c).group(1)
    fold[p] = (f, int(nf), int(nl), int(nt), int(nd))
build = {}
for line in open(os.path.join(D, 'clean_build_by_folder.txt')):
    f, m, s, g = line.split(); build[f] = (int(m), int(s), float(g))
tar = {}
for line in open(os.path.join(D, 'tarballs_downloads.txt')):
    n, h, d, t = line.split(); tar[int(n)] = (h, d, t)

out = []
out.append('**Table 6a. Provenance.**\n')
out.append('| Piece | Aristotle task | Tarball | md5 | Downloaded | Brute force before sending |')
out.append('|---|---|---|---|---|---|')
for p in PIECES:
    n = TAR[p]; h, d, t = tar[n]
    _, fi, ct = BF[p]
    nc, nk = checks_from_log(p)
    cks = f'{nc:,}'.replace(',', ' ') + ' checks' + (f' in {nk} kind' + ('s' if nk > 1 else '') if nk else '') + ', 0 failures'
    ctl = f'controls {fi}/{ct}' + (' (one silent, declared)' if fi < ct else '')
    lab = '—' if n == 0 else f'({n})'
    out.append(f'| C{p} | `{TASK[p]}` | {lab} | `{h[:8]}` | {d[8:10]}/{d[5:7]} {t} | {cks}; {ctl} |')
out.append('')
out.append('**Table 6b. The Lean folders and their clean rebuild.**\n')
out.append('| Piece | Folder | Files | Lines | `theorem`/`lemma` lines | Definitions | Modules | Rebuild s | Peak GiB |')
out.append('|---|---|---|---|---|---|---|---|---|')
tot = [0, 0, 0, 0, 0, 0]
for p in PIECES:
    f, nf, nl, nt, nd = fold[p]; m, s, g = build[f]
    assert m == nf, (p, f, m, nf)
    out.append(f'| C{p} | `{f}` | {nf} | {nl:,} | {nt} | {nd} | {m} | {s:,} | {g:.2f} |'.replace(',', ' '))
    for i, v in enumerate((nf, nl, nt, nd, m, s)): tot[i] += v
m, s, g = build['Main']
out.append(f'| — | `Main.lean` | 1 | 24 | 0 | 0 | {m} | {s} | {g:.2f} |')
pk = max(v[2] for v in build.values())
out.append(f'| **Total** | 69 folders + `Main.lean` | **{tot[0]+1}** | **{tot[1]+24:,}** | **{tot[2]:,}** | **{tot[3]}** | **{tot[4]+m}** | **{tot[5]+s:,}** | **{pk:.2f}** |'.replace(',', ' '))
open(os.path.join(D, 'tables.md'), 'w').write('\n'.join(out) + '\n')
print('pieces', len(PIECES), 'files', tot[0], 'lines', tot[1], 'theorems', tot[2], 'defs', tot[3],
      'modules', tot[4] + m, 'seconds', tot[5] + s, 'peak', pk)

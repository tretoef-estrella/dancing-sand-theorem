# REPORT_COLD_9 — cold reading 9: the changes of version 7 of «The Dancing Sand Theorem»
Reader: Grepy el lector frío del cubo 9.

## 0. First lines

- **Do the changes of version 7 hold as written? HOLDS WITH GAPS.** No numbered statement changed: no symbol, quantifier or hypothesis; the one proof step touched (Proposition 9.6 (H)) is now more exact. Every changed sentence checks out against the text, the two logs, the arithmetic of the houses (43 690, 65 532, 16 380), `gate_strict_cut.py` (re-run: all its numbers reproduced), Propositions 4.1–4.2 and the source of [LZ22]. The pages that changed are exactly the author's list (1, 2, 3, 9, 30, 44, 46–52), and nothing on them is broken. md = pdf on every changed passage. The acceptance list passes 9 of 9, and its controls fire 9 of 9, each damage acting on its own check. Every defect of reading 8 is fixed. **One sentence of the record is false:** App. A, the «Version 7» entry, «No mathematical statement changed, and no number» — v7 changes printed numbers (the dates of the work; the split reader-3 row of §12.2). Nothing mathematical is affected.
- **Is version 7 ready to be sent? AFTER CORRECTIONS:**
  1. **(ERROR, record)** pdf p. 51, Appendix A, item «Version 7 (this text)», line 2 (md l. 1152). Replace «No mathematical statement changed, and no number.» by «No mathematical statement changed; the row of the third reader on the lattices `T(λ)` now gives its two runs separately (639 + 762 = 1 401 cells, 102 + 172 = 274), and the dates of the work were corrected.» (§2.9)
  2. **(PRESENTATION, recommended)** same item, line 1. Replace «and says in §12 which ranges of houses include `k = 0`.» by «says in §12 and in this appendix which ranges of houses include `k = 0`, and makes three sentences more exact (§1.0, Proposition 9.6 (H), [LZ22]).» (§2.9)
  Nothing else. The same false sentence is in CORRECTIONS_v6_to_v7.md, along with «The other 39 pages are unchanged» (it is 38). That note does not go to the outside reader.

## 1. The hunks of the diff

My own `diff -u` of the v6 and v7 md gives the same 10 hunks, byte for byte apart from the two timestamp lines (`logs/diff_check.log`, VIGIA-FIN-OK). No hunk touches the statement of a numbered result (Theorem, Lemma, Proposition, Corollary). One hunk touches a proof step (Proposition 9.6 (H)), with the same mathematical content. Hunk by hunk (v6 line numbers):

| # | where | what changed | numbered statement / proof step? | content? | verdict |
|---|---|---|---|---|---|
| 1 | header (l. 6) | «version 6» → «version 7» | no | record | HOLDS |
| 2 | §1.0 (l. 32) | «§7.1, §7.4, §9.2» → «§7.1, §7.4, §7.5, §9.2»; «this version 6» → «version 6»; new sentence on the eighth reading; «version 6» → «version 7» not read cold | no | record | HOLDS (see §2: the §-list matches the places named in App. A) |
| 3 | §1.7 «Why dance» (l. 196) | «the payment minus half the product» → «a payment equal to minus half the product» | no | wording only, same meaning as Props 4.1–4.2 | HOLDS |
| 4 | Prop 9.6, proof (H) (l. 746) | «if its value is positive» → «if `Z_1` is positive there» | proof step | same step, the condition now names the right function | HOLDS |
| 5 | §12.1, row of `gate_strict_cut.py` (l. 1068) | «`k ≤ 6`» → «`1 ≤ k ≤ 6`» | no | range made exact; no number | HOLDS |
| 6 | §12.2, four rows (l. 1094–1101) | reader 3, Theorem 7.8: «(`k = 0` included)»; reader 3, `T(λ)`: row rewritten with both runs (1 401 → 639 and 762; 274 → 102 and 172; new: 43 and 372 skipped, `λ ≤ 31, i ≤ 10`); reader 4 (two rows) and reader 5: «`k ≤ 7`» → «`1 ≤ k ≤ 7`» | no | ranges made exact; one row's numbers split by run | HOLDS (numbers checked in §2) |
| 7 | §12.2, reader 6 row (l. 1112) | «`k ≤ 6`» → «`1 ≤ k ≤ 6`» | no | range made exact | HOLDS |
| 8 | §13 (l. 1117–1124) | the eighth reading added to «Proved…»; the sentence on versions 2 to 7 rewritten; v6 now «read cold»; new line for v7; «Not done» now v7 | no | record | HOLDS (see §2) |
| 9 | Acknowledgements (l. 1135) | «four days, from 2 to 5 October» → «five days, from 2 to 6 October» | no | record (a number) | HOLDS |
| 10 | App. A (l. 1146–1150) and [LZ22] (l. 1176) | reader 4's range «`k ≤ 7`» → «`1 ≤ k ≤ 7`, `α ≤ 3`»; v6 entry now records reading 8; new v7 entry; [LZ22] gains «with an appendix by S. Casalaina-Martin» | no | record; reference | HOLDS, except one sentence of the v7 entry (§2, item 2.9: ERROR of the record) |

No symbol, quantifier or hypothesis of a numbered statement changed. Numbers that changed: the version number; the day count and last date of the work; the reader-3 `T(λ)` row (1 401 and 274 replaced by their parts, and 43, 372, 31, 10 added).

## 2. The changed sentences, one by one

**2.1 §13, the sentence on versions 2 to 7 — HOLDS.** Each statement it names, against the text of v7:
- Theorem 7.8 (v7 l. 629–640): (Cut) says «these cuts are **strict**: `fit(x_H)` is larger at the dancer before `b` than at `b`». Strictness is there. ✔
- Lemma 7.2(b) (l. 566–571): the restated form, with the integer claim only under «`δ` integer and constant on every level set … in particular, if every position at which `δ` changes is a strict cut», and the counterexample `x = (3,4,3,4)` in the proof. ✔
- Lemma 7.9 (l. 671): «(integrality)» — the real fit of `x_H`, of every penalty cell and of the deletion is integral. ✔
- Lemma 10.6(a) (l. 866): «For an **even** payment system …». ✔
- Lemma 10.10 (l. 899): «For every `L ≥ 0` and every floor `f`, …». ✔
Against Appendix A: v2 «restates Lemma 7.2(b), adds strict (Cut) to Theorem 7.8» ✔; v3 «states that integrality as Lemma 7.9, makes all the corrections above», which include the word «even» found missing in Lemma 10.6(a) ✔; v4, v5, v6, v7 each «No mathematical statement changed» ✔. The change of Lemma 10.10 is not named in Appendix A (only in §13); no sentence of Appendix A contradicts it. «No other numbered statement changed in versions 2 to 7»: for v6→v7 I verified it on the diff (no statement line is touched); for v2–v6 the record I have (v6, v7, the diff) shows nothing against it. Remark (2) of §10.5 changed in v2 and v3 (App. A), but a remark is not a numbered statement (style doubt 7.1). The old defect (v6 said «no other statement» and then named three lemmas) is gone: the lemmas are now named before «no other».

**2.2 §1.0, «Version 2 repaired it (§7.1, §7.4, §7.5, §9.2)» — HOLDS.** §7.1 holds Lemma 7.2(b), §7.4 Theorem 7.8, §7.5 Lemma 7.9 and Theorem 7.10, §9.2 Proposition 9.6: exactly the places that App. A says used the false integer part (Theorem 7.8 step 1, Lemma 7.9, Theorem 7.10, Proposition 9.6) and §13 says were repaired.

**2.3 §12.2, the row on the lattices `T(λ)` — HOLDS.** Every number against the two logs (both end in VIGIA-FIN-OK, TOTAL FAIL COUNT: 0):

| printed | `family_lattice_31_10.log` | `family_lattice_63_8.log` |
|---|---|---|
| ranges `λ ≤ 31, i ≤ 10` / `λ ≤ 63, i ≤ 8`, `α = 1, 2` | `lambda <= 31, 0 <= i <= 10, alpha in (1,2)` ✔ | `lambda <= 63, 0 <= i <= 8, alpha in (1,2)` ✔ |
| skipped, predicted exponent ≥ 60: 43 and 372 | `SKIPPED (predicted exponent >= 60): 43` ✔ | `372` ✔ |
| compared: 639 and 762, 0 failures | `cells compared: 639`, FAIL 0 ✔ | `762`, FAIL 0 ✔ |
| raw clocks rejected in all 102 and 172 cells where pooling acts | `CONTROL raw rejected: 102`, `pooling acts: 102` ✔ | `172`, `172` ✔ |

The old row's 1 401 and 274 are the sums (639 + 762, 102 + 172) printed under the range of the second run only: the defect reader 8 found, now fixed. Consistency: 639 + 43 = 682 = 31·11·2 and 762 + 372 = 1 134 = 63·9·2, i.e. `λ` from 1, `i` from 0 (the logs do not print these totals; an inference, not a check).

**2.4 §12 and Appendix A, the ranges of houses — HOLDS.** With `4^k` houses for each `(k, α)` (§7.3: `I ⊆ [0, k)`, `0 ≤ ℓ < 2^k`) and `α ≥ 1`:
- `Σ_{k=0}^{7} 4^k = 21 845`, `× 2 = 43 690` → reader 3, «`k ≤ 7` (`k = 0` included), `α = 1, 2`» ✔ (without `k = 0` it would be 43 688);
- `Σ_{k=1}^{7} 4^k = 21 844`, `× 3 = 65 532` → reader 4 (two rows and App. A) and reader 5, «`1 ≤ k ≤ 7`, `α ≤ 3`» ✔ (with `k = 0`: 65 535). REPORT_COLD_4 (the only lines I read, those with «65 532»: l. 7, 117, 138, 357) says «65 532 houses (`k ≤ 7`, `α ≤ 3`)»; it does not write `1 ≤`, but the number forces it. ✔ The App. A range «`1 ≤ k ≤ 7`, `α ≤ 3`» is the one in that report (the scribe's slip «`α = 1, 2`» recorded in CORRECTIONS is not in the text).
- `Σ_{k=1}^{6} 4^k = 5 460`, `× 3 = 16 380` → `gate_strict_cut.py` row of §12.1 and reader 6, «`1 ≤ k ≤ 6`, `α ≤ 3`» ✔ (with `k = 0`: 16 383). The code: `for k in range(1,K_MAX+1)` and `for a in (1,2,3)` (l. 37, 46) — `k = 0` is excluded. My run of the code (`logs/gate_k6.log`) — see 2.4bis.
- Side checks that agree: deletions are the houses with `ℓ = 2^k − 1`, `I ≠ ∅`: `3·Σ_{k=1}^{6}(2^k − 1) = 360` and `3·Σ_{k=1}^{7}(2^k − 1) = 741` ✔; Theorem 7.8 row of §12.1, `I ≠ ∅`, `k ≤ 6`: `3·Σ_{k=1}^{6}(4^k − 2^k) = 16 002` ✔. The reader-5 row keeps «the 8 001 houses with `k ≤ 6` that have a boundary»: a house with `k = 0` has no boundary, so the set is the same.

**2.4bis My run of `gate_strict_cut.py 6 4`** (a copy in `scratch/`, `logs/gate_k6.log`, VIGIA-FIN-OK, 42 s, 11 MB): `houses 16380, bnd 8001, strict_fail 0, pen_checks 192024, pen_fail 0, del_checks 360, del_fail 0, nonint 0`; controls `1911 of 7038`, `18606 of 192024`, `1942`. Every number of the two `gate_strict_cut.py` rows of §12.1 is reproduced, and the 16 380 houses are those with `1 ≤ k ≤ 6`, `α ≤ 3`. ✔

**2.5 §1.7 «Why dance» — HOLDS.** «each move gives every new floor a payment equal to minus half the product of the payments of two adjacent old floors»: Proposition 4.1, `π'_s(f) = −π_s(2f) π_s(2f+1)/2` (old floors `2f`, `2f+1`); Proposition 4.2, `π''_{(s,A)}(f) = −π_s(2f)π_s(2f+1)/2` and `π''_{(s,C)}(f) = −π_s(2f+1)π_s(2f+2)/2` (old floors `2f, 2f+1` and `2f+1, 2f+2`). Each is minus half the product of two adjacent old payments ✔. «so every payment stays even»: half a product of two elements of `2A` is in `2A` (proof of 4.1) ✔. The v6 phrase «the payment minus half the product» could be read as a difference; the new one cannot. (The sentence speaks of payments only, not of couplings; it does not claim more.)

**2.6 Proposition 9.6 (H), «if `Z_1` is positive there» — HOLDS, exact.** Here `Z_1 = fit(x_{H'}) + d_1` is the real fit of the first half, with the level sets of `fit(x_{H'})` (Lemma 7.2(b), `d_1` changes only at strict cuts); «there» is the first level set `L` of `fit(x_{H'})`, on which `Z_1` is constant. By Lemma 7.3 the fit on the first half is `max(Z_1, 0)`. If `Z_1(L) > 0`, the next level set of `Z_1` has a strictly smaller value, so `max(Z_1, 0)` drops strictly after `L` and `L` is the first level set ✔. If `Z_1(L) ≤ 0`, then `Z_1 ≤ 0` on the whole first half (it is non-increasing), `max(Z_1,0) = 0` there and `min(Z_2,0) = 0` on the second half, so the fit is `0` everywhere and the first level set is everything ✔ — the «otherwise» clause is the exact negation. The v6 «if its value is positive» could be read as the value of `fit(x_{H'})`, which is not the right condition (`d_1` may be negative); the new wording names the right function.

**2.7 [LZ22] — HOLDS.** The source (arXiv:2012.15235v4, 6 Mar 2022) has, in its abstract, «the appendix by Sebastian Casalaina-Martin», and in its contents «Appendix A. The algebraic Abel–Prym map (by Sebastian Casalaina-Martin)». «with an appendix by S. Casalaina-Martin» ✔. Authors, title and arXiv number agree. The journal data (*Forum Math. Sigma* 10 (2022), e11) is not in the arXiv text, so I cannot check it from the source (unchanged in v7).

**2.8 The record: header, §1.0, §13, Acknowledgements, Appendix A — HOLDS, with one exception (2.9).** Inside the text the sentences on the readings agree with each other:
- reading 8: §1.0 «The changes of version 6, and its whole pdf page by page, were read cold by an eighth reader … holds … nothing on the page is broken … two false sentences in the record of the work, one row of §12.2 …, one sentence of §1.7» = App. A v6 entry (same four findings, named) = §13 «the changes of version 6, with its whole pdf, by an eighth» ✔; date 6 October 2026 (App. A) ✔.
- version 7 «made by the auditor, not yet read cold» in §1.0 (bold), §13 (two lines: «Changed in version 7 …», «Not done: a cold reading of the changes of version 7») and App. A ✔. «Changed in version 6, read cold» ✔.
- Acknowledgements «five days, from 2 to 6 October 2026»: 2, 3, 4, 5, 6 = five days ✔; it agrees with App. A (flights 3–5 October, readings 7 and 8 on 6 October) and the header date ✔.
- What is said to be left undone: only a cold reading of v7, a human referee, a formal verification (§13); and, from v4, «except two defects of typesetting» (old record). Nothing of reading 8 is said to be left undone. Whether App. A's description of how reader 8 worked («opened the seventh reading only after writing its verdicts», «compared the md and the pdf word by word», «checked every cross-reference and every quotation») is exact cannot be seen inside the text; I check it in §6.

**2.9 Appendix A, v7 entry, «No mathematical statement changed, and no number.» — ERROR (of the record, not of the mathematics).** The first half holds. The second is false as written: v7 changes printed numbers — the day count and last date in the Acknowledgements («four days … to 5 October» → «five days … to 6 October»), and the reader-3 `T(λ)` row of §12.2, where «1 401 cells» and «274 cells» are replaced by «639 and 762» and «102 and 172», and «43 and 372» and the range «`λ ≤ 31`, `i ≤ 10`» are new. No number of a result became different in value (the old ones are the sums), so nothing mathematical is affected. CORRECTIONS_v6_to_v7.md repeats the same sentence. **Fix (pdf p. 51, App. A, the «Version 7» item, line 2; md l. 1152):** «No mathematical statement changed; the row of the third reader on the lattices `T(λ)` now gives its two runs separately (639 + 762 = 1 401 cells, 102 + 172 = 274), and the dates of the work were corrected.» Also, the same entry says only «and says in §12 which ranges of houses include `k = 0`», but the range was also changed in App. A (reader 4: «`1 ≤ k ≤ 7`, `α ≤ 3`»), and three other edits of v7 are not recorded anywhere in the text (§1.0 «§7.5», the wording of Proposition 9.6 (H), [LZ22]) — PRESENTATION, harmless; fix: §0, item 2.

## 3. The changed pages (the list is in `checks/PAGES.md`)

**HOLDS.** I rendered both pdfs at 72 dpi and compared the page bitmaps by md5 (`logs/render_cmp.log`, VIGIA-FIN-OK): both have 52 pages, and the pages that differ are exactly **1, 2, 3, 9, 30, 44, 46–52** — the author's list. That is 14 pages; the other **38** pages are identical bitmaps (CORRECTIONS says «The other 39 pages are unchanged»: 52 − 14 = 38, a slip of the author's note, not of the paper). I looked at each of the 14 pages at 90 dpi (`scratch/p90/`): every changed passage is on the page, and nothing is broken. One line per page in `checks/PAGES.md`. Page 46 ends ~15 % short because a table row is not broken across a page (the house rule); p. 48 has one loose justified line in §13 — neither counted.

## 4. md against pdf on the changed passages

**HOLDS.** My script `scratch/md_vs_pdf9.py` takes the 21 non-empty lines added by the diff and checks, in `pdftotext` of the v7 pdf, that (i) the words of each line (table rows: of each cell) occur in the same order and contiguously, and (ii) every digit run of the line occurs (`logs/mdpdf.log`, VIGIA-FIN-OK). Result on v7: 63 checks, **1 miss**, an artefact: the reader-6 row ends «no non-integral fit», set in the pdf with «non-» at the end of a cell line (p. 48, seen on the page), and `pdftotext` drops line-end hyphens, giving «nonintegral». The same miss appears on the v6 pdf, where that cell is unchanged.
Controls, both fire: (a) the same script on the **v6** pdf misses 17 checks (every line whose words or numbers changed: §1.0, §1.7, Proposition 9.6, the `T(λ)` row with its numbers 639, 762, 102, 172, §13, the Acknowledgements, App. A, [LZ22]); (b) on v7 with the longest word of every line replaced by a nonsense word, it misses 22 checks, every line.
The word-and-number check cannot see changes of symbols only (`k ≤ 6` → `1 ≤ k ≤ 6`, «version 6» → «version 7»). For those I counted strings in both texts: «1 ≤ k ≤ 6» v7 pdf 2 = md 2 (v6 pdf 0); «1 ≤ k ≤ 7» v7 pdf 4 = md 4 (v6 pdf 0); «k = 0 included» 1 (v6 0); «version 7» 5 = md 5; «Z1 is positive there» 1 (v6 0); «§7.5, §9.2» 1 (v6 0). And I saw each on its page at 90 dpi (§3).

## 5. The acceptance list and its controls

**HOLDS.** The two mission commands, run as written (`logs/acc_v7.log`, `logs/acc_v7_control.log`, both VIGIA-FIN-OK, 2 s, ≤ 117 MB): on v7 **9 of 9 PASS**; in control mode **9 of 9 FAIL** («controls fired: 9 of 9»). The author's claims hold. The numbers of check 9 agree with CORRECTIONS: 32 reference keys, all cited and all listed; unresolved only the five external items (Gao et al.'s Theorems 4.1, 4.2 and Proposition 2.5; [Hum72, §26]; [CSX17, §5.2]); md = pdf on 108 + 7 + 16 numbers of §12, §1.0–§1.4, §13 + App. A, DIFFERENCES 0. Check 6 lists two lines of the changed p. 48 at 2.01× (under the 3× limit). An extra run on v6 (`logs/acc_v6.log`) also passes 9 of 9.

The damages of the control mode, read in `acceptance.py` (l. 26–35, 46, 143, 159–160), and what the control log shows each one doing:

| check | damage | acts on its check? (control log) |
|---|---|---|
| 1 list numbers | `RAWNS`: «2.(Λ).» → «(Λ).» (step 2 of the proof of Theorem 7.8 loses its number) | yes: «2. (Λ).» reported |
| 2 md words | md: «the dance of» → «the dance off» | yes: «off: md 7, pdf 6» is listed. **But** the check would fail without it: the page-10 damage of check 5 deletes words from the bbox, and check 2 lists 38 lost words, 37 of them from that cut. Its «fired» alone proves nothing; the listing does. (style doubt 7.3) |
| 3 margins | bbox: the first `xMax="54…"` → `"56…"` | yes: «words beyond it: 1, max 561.8» (right edge 542). Position-dependent: it relies on the first such word ending at 54x pt, not 54.x pt (true here) |
| 4 widows | bbox: «widow end.» inserted at the top of pages 1 and 2 | yes: «p. 2: «widow end.»» (page 1 skipped by design) |
| 5 page fill | bbox: page 10 loses every word with `yMin` 450–799 | yes: «p. 10: 55.9 % (next page begins «Up to the sign …»)», not before a section |
| 6 loose lines | bbox: a line «alpha beta gamma delta» with 12 pt gaps on page 1 | yes: «12.00 pt (3.44x) p1 y=10 text alpha beta gamma delta» |
| 7 fonts and glyphs | `raw + '�'` | yes: «missing or private glyphs: 1» |
| 8 hyphenation | `bw + ['spa‐', 'ces']` (a known wrong break) | yes: ««spa-/ces»» |
| 9 xrefs and numbers | md9: «43 690 houses» → «43 691 houses»; the first «Lemma 7.9 (integrality)» → «Lemma 7.99 (integrality) by Lemma 7.99» | yes, both: numbers «replace md ['43691'] pdf ['43690']», DIFFERENCES 1; xrefs: the first occurrence is the statement itself, so Lemma 7.9 is no longer defined and 25 citations of it become unresolved (27 with the two externals) |

So each damage acts on the check it is meant for. The isolation is not perfect (check 2 is also hit by the damage of check 5), which weakens what the bare count «9 of 9» says, but not the result: each check's own damage is visible in its own output.

The tools printed «for reading» and not judged in check 9 (the author's `xrefs.py` and `md_vs_pdf.py`) report «MISSING TARGET» lines (labels of the summary table and external items) and, in `md_vs_pdf.py`, «NOT a subsequence» for the §1.0 and §12.1 tables and 4 statements «not matched in order» (Lemma 2.1, Corollary 2.3, Lemma 9.7, Lemma 10.11). The same lines appear on v6 (`logs/acc_v6.log`; only the number counts move with the new text), they concern unchanged passages, and my own md-vs-pdf check of the changed passages (§4) is clean. I did not investigate them (§10).

## 6. After everything else (§4)

Opened only after §1–§5 of this report were on disk (`logs/DIARY.md`, line «BEFORE §6: opening material/read_after/ now that §2 is written»). Read whole: `REPORT_COLD_8.md`, `CALIFICACION_LECTOR_FRIO_8_v1.md`.

**Every defect of reading 8 is fixed in v7, with the fix it proposed or an equivalent one.**

| defect (reading 8) | its fix | in v7 | verdict |
|---|---|---|---|
| **E1** §13: «no other statement of a theorem changed in versions 2 to 6», then three lemmas of v3 named | «Version 2 added …; version 3 strengthened Lemma 7.9, added … to Lemma 10.6(a) and … to Lemma 10.10; no other numbered statement changed in versions 2 to 6.» | the proposed wording, with «2 to 7» and «, and added the explicit quantifier» (md l. 1117, p. 48) | **fixed, as proposed** |
| **E2** Acknowledgements «four days, from 2 to 5 October» | «five days, from 2 to 6 October 2026» | identical (md l. 1136, p. 49) | **fixed, as proposed** |
| **E3** §12.2 reader-3 `T(λ)` row: 1 401 / 274 do not fit the printed range (1 134 cells, 218 with pooling) | «take the range that reader 3 actually ran from its log … and print it» | both runs printed from the two logs, with the skipped cells (§2.3). Reader 8's counts agree with the logs: 762 + 372 = 1 134 for the second run, and its 218 pooling cells over that whole range ≥ the 172 among the compared ones | **fixed, equivalent (the fix it named first)** |
| **D1** «Why dance» reads as a subtraction | «a payment equal to minus half the product» | identical (md l. 196, p. 9) | **fixed, as proposed** |
| taste: Prop 9.6 (H) «its value» | name `Z_1` | «if `Z_1` is positive there» | fixed (§2.6) |
| taste: §1.0 could add §7.5 | add it | «(§7.1, §7.4, §7.5, §9.2)» | fixed |
| taste: [LZ22] lacks the appendix | add it | «with an appendix by S. Casalaina-Martin» | fixed (§2.7) |
| taste: `k = 0` counted in 43 690, not in 65 532 | — | ranges now say «`k = 0` included» / «`1 ≤ k`» | fixed (§2.4) |
| taste: comma after display matrices (pp. 34–35), `X^ι` (p. 11), bold of Cor. 1.6 bullets (p. 6), `W_−` (p. 42) | — | not applied (those pages are identical bitmaps) | style, as the grading says; not defects |
| A1 dead controls of checks 1 and 4; A2/A3 check 9 cut and not judged; no control for 5, 6 | repair the list | the damages of 1, 4, 5, 6, 8 act, check 9 prints whole and is judged (§5) | **fixed** |

The record of reading 8 in v7, against its report: «no access to the flights or the audits» — consistent (its report never cites them); «opened the seventh reading only after writing its verdicts» — its §6 says so ✔; «compared every change with version 5» (its §1.1, word diff) ✔; «re-counted the numbers of §12 with its own code» (§1.3) ✔; «compared the md and the pdf word by word and number by number» (§3.1) ✔; «checked every cross-reference and every quotation against its source» (§3.2, §3.3: nine quotations verbatim) ✔; «looked at every page» (52 of 52) ✔; «the mathematics of every change holds, and nothing on the page is broken» — its §0: «every change of wording keeps the mathematics», «on 52 pages I found nothing broken» ✔. Its own headline verdicts were «HOLDS WITH GAPS» and «Is the pdf correct? NO — 4 defects»; the text gives the content, not the words (style doubt 7.2). The four findings are named exactly; «one row of §12.2 that printed only one of the two ranges its reader ran» is the author's diagnosis of reading 8's E3, settled afterwards from reader 3's logs (CALIFICACION, item 4) — true of the row, but reading 8 itself said only that the row did not fit its range (style doubt 7.2). The date (6 October 2026) is not in the report; nothing contradicts it.

Reading 8 did not see my finding (App. A v7 «and no number»): it is new in v7.

## 7. Style doubts (not counted)

- **7.1** §13 «no other numbered statement changed in versions 2 to 7»: Remark (2) of §10.5 changed in v2 and v3 (App. A). A remark is not a numbered statement, so the sentence holds. A careful reader might still ask about it.
- **7.2** App. A, «Version 6» entry, and §1.0: reading 8's findings are given in the author's words. «one row of §12.2 that printed only one of the two ranges its reader ran» is the diagnosis made afterwards from reader 3's logs (reading 8 said the row did not fit its range). Reading 8's own verdicts («holds with gaps»; «pdf correct? NO — 4 defects») are not quoted, though reading 3's «holds with gaps» is. True, but gentler than the report.
- **7.3** `acceptance.py`, control mode: the damage of check 5 (half of page 10 deleted) also makes check 2 fail, so «9 of 9 fired» does not by itself show that check 2's own damage is caught. The listing does show it («off: md 7, pdf 6»). Check 3's damage depends on the first `xMax="54…"` being a word at 54x pt.
- **7.4** App. A, «Version 6» entry, quotes v6's sentence as «no other statement». The v6 text said «no other statement of a theorem». The trim is harmless (reading 8 argued the generic reading), but it is a trimmed quotation in a text that faulted one in [Aky26].
- **7.5** The change of Lemma 10.10 in v3 (the quantifier) is recorded only in §13, not in App. A.
- **7.6** Prop. 9.6 (H), the unchanged words after the edit: «the fit vanishes on the whole level» — «level» means the whole sequence of the cell. «on the whole sequence» would be plainer.
- **7.7** p. 46 ends ~15 % short (a table row is not broken), and p. 48 has a loose justified line in §13 (2.01×). Both are house rules or TeX-like breaks, not defects.
- **7.8** The tools that `acceptance.py` prints «for reading» (`xrefs.py`, `md_vs_pdf.py`) still print «MISSING TARGET» and «NOT a subsequence» lines that are known artefacts. Anyone reading the log has to know to ignore them.

## 8. Sealed predictions, hits and failures

Sealed in `checks/SEALED.md` before any measurement (diary line «SEALED P1–P7»). **7 predictions: 7 hits, 0 failures.**
- P1 (my diff = their diff, 10 hunks): **hit** (`logs/diff_check.log`).
- P2 (43 690, 65 532, 16 380 by arithmetic, `k = 0` as printed): **hit**.
- P3 (the `T(λ)` row = the logs; 1 401 and 274 are the sums): **hit** for every printed number. The totals 682 and 1 134 are not in the logs; 1 134 agrees with reading 8's own enumeration (`REPORT_COLD_8` §1.3, E3).
- P4 (`gate_strict_cut.py` loops `k` from 1 to 6, `α = 1, 2, 3`): **hit**, by reading and by running.
- P5 (changed pages = 1, 2, 3, 9, 30, 44, 46–52, both 52 pages): **hit**.
- P6 (9/9 pass, 9/9 fire, both VIGIA-FIN-OK): **hit**.
- P7 (the §13 sentence consistent with App. A, at most a presentation point): **hit** for §13. What I did not predict is the false sentence I found, which is in App. A's v7 entry, not in §13.

## 9. My errors

- **M1.** `echo ======` in zsh (a word starting with `=`), in the command that showed the tails of the two acceptance logs. zsh stopped there. Harmless: both runs had already finished and their logs were complete. Noted at once in the diary.
- **M2.** One command `cd material/tools && …` (to read the helper scripts) left the shell in `material/tools/` for the next command, which was read-only. Nothing was written there.
- **M3.** I first wrote «pdf p. 52» for the App. A v7 entry (§2.9). It is on p. 51, which I saw when I looked at the pages. Corrected in the report and noted in the diary.
- **M4.** I first wrote «37 lost words, 36 from the cut» in §5. From the log it is 38 and 37. Corrected.
- **M5.** Light work outside `vigia.sh`: the first md5 check of the material against the manifest, one count of strings in the two pdf texts (§4), and the `python3` heredocs that wrote sections of this report. All took seconds and a few MB. Every real run (diff, gate, renders, md-vs-pdf, acceptance ×3, md5) went through the watchdog.
- **M6.** The diary line for the first md5 check was written as a placeholder and then filled in with `sed`. The time on it is when it was filled in (seconds later), not when the check ran.

## 10. What I did not read

- **The unchanged parts of the paper** (as the mission says): I read §1.0, §1.7 «Why dance», §4.1–§4.3, §7 whole, Prop. 9.6 (H), Lemmas 10.6 and 10.10 (statements), the Remarks of §10.5, §12, §13, the Acknowledgements, App. A and [LZ22]. I re-proved nothing else.
- **`THE_DANCING_SAND_THEOREM_v7.html`:** not read.
- **`REPORT_COLD_4.md`:** only the four lines that contain «65 532» (l. 7, 117, 138, 357), as the mission says.
- **The source of [LZ22]:** the text file (abstract, contents, grep). The pdf was not opened. The journal data (*Forum Math. Sigma* 10, e11) is not in the arXiv text, so it is not verified.
- **Tools:** I read `acceptance.py`, `fill.py`, `loose.py`, `xrefs_reader8.py`, `numbers_reader8.py`. I did not read `xrefs.py` or `md_vs_pdf.py` (printed «for reading», not judged), nor `margins.py`, `glyphs.py` (not called). I did not look into the «NOT a subsequence» and «not matched in order» lines of `md_vs_pdf.py`; they are the same on v6 and concern unchanged passages.
- **Versions 1–5** are not in this folder, so «no other numbered statement changed in versions 2 to 5» can only be checked for consistency with the record of v7, not against the texts.
- **Reader 3's report** is not here; the CALIFICACION says «Reader 3's own report gives both ranges». I checked the row against the two logs only.

## 11. Files with md5

Computed under the watchdog (`logs/md5_final.log`, VIGIA-FIN-OK). At the end, `material/`, `vigia.sh`, `MISSION.md` and `CLAUDE.md` still match `MANIFEST_md5.txt` (`logs/md5_material.log`, «MATERIAL_UNCHANGED»). Not in the table, because they change after it: `REPORT_COLD_9.md` (its md5 is on the last line of `logs/DIARY.md`), `logs/DIARY.md`, `ESTADO.md`, `logs/md5_final.log`, `logs/md5_material.log`, `scratch/md5_material_end.txt`. `scratch/gate_strict_cut_copy.py` = `material/evidence/gate_strict_cut.py` (same md5). The 104 page bitmaps of `scratch/r6/`, `scratch/r7/` (72 dpi): md5 of their `md5 -r` list `fbf9781433b1961ed894332c74b4af8c`. `scratch/tmp/` holds the 3 temporary folders of `acceptance.py`. Nothing in `scratch/_BORRAR/`. Nothing was written outside this folder.

| md5 | file |
|---|---|
| cb883e8380c2aaba1ab446a4c000ff26 | checks/PAGES.md |
| c3d2df0c0ebda81eae397feb592a48ca | checks/SEALED.md |
| f39722fb6be19347fabf32505ec8373e | scratch/md_vs_pdf9.py |
| 150c315bfd45c8060170bc407c78feed | scratch/gate_strict_cut_copy.py |
| 2166ffe04bd5a1f946aaa0f8f51a4019 | scratch/mydiff.txt |
| 85bcca1a7b80afff25a631e22bd1e3d2 | scratch/v6.txt |
| f573ab029e52c241d8e4274981e3d94f | scratch/v7.txt |
| aa3e6f1c16d31fca485b1aa3da3c8b5e | logs/diff_check.log |
| e6646d9c608d005189c97f3d784413e6 | logs/gate_k6.log |
| 72499e7752cdd30d00b5dc4c64347f66 | logs/render_cmp.log |
| e7e9c6fff740a1b072af1a0b86c87a39 | logs/render90.log |
| 1b834cbd5b45420cb8f0f09b7a826495 | logs/mdpdf.log |
| 1101b935228d47858b2e588cee929230 | logs/acc_v7.log |
| 9154d5603c7db6ba9961de059cf77e89 | logs/acc_v7_control.log |
| c075d933be10fe48715f3990b0f38be0 | logs/acc_v6.log |
| 5b88b6f349f2f7df6ba518226966845a | scratch/p90/v7-01.png |
| 44993cbd253e7e47172e7b0e1bf796d5 | scratch/p90/v7-02.png |
| 500a20dce99807481e483e2b162662a5 | scratch/p90/v7-03.png |
| 8d19b098d276bc3c4f581e57016c7a0a | scratch/p90/v7-09.png |
| 82aa567365b1aaa7720aad48488c2830 | scratch/p90/v7-30.png |
| 3b8f21acab640bbea34e4ee95eec2c16 | scratch/p90/v7-44.png |
| 3e96871bbe93c014937c030ed11b644b | scratch/p90/v7-46.png |
| 23d0cea8496862219368a33d12f7b46b | scratch/p90/v7-47.png |
| 96d49936dc5823767127429714d193ea | scratch/p90/v7-48.png |
| 48383ab4a32fc49098fa602aaaf86c23 | scratch/p90/v7-49.png |
| c03c334ff0b8d8198b748a3617f0024d | scratch/p90/v7-50.png |
| f8f72329609d7e2b7c91bc32e90649f5 | scratch/p90/v7-51.png |
| 6e953b00ef9d6c57d7d95b01bf4f699f | scratch/p90/v7-52.png |

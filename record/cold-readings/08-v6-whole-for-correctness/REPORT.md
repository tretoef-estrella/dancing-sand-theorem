# REPORT_COLD_8 — cold reading 8 of «The Dancing Sand Theorem», version 6

Reader: Grepy el lector frío del cubo 8.

## 0. First lines

- **Do the changes of version 6 hold as written? HOLDS WITH GAPS.** No symbol, number, quantifier or hypothesis of any statement or proof step changed; every change of wording keeps the mathematics, and every item of CORRECTIONS §1–§2 is done in the md and in the pdf. But two of the changes are not exact as written: the rewritten sentence of §13 is still false (E1), and the new «Why dance» sentence reads as a subtraction (D1).
- **Is the pdf correct? NO — 4 defects** by the standard of §1 (3 ERROR, 1 PRESENTATION), all of them sentences or numbers of the text, none in the mathematics of the statements or proofs, none of the page: on 52 pages I found nothing broken, no lost word, number, label or list number, no missing glyph, and md = pdf.
- **Is version 6 ready for publication? AFTER CORRECTIONS:**
  1. **E1** — p. 48, §13, bullet «Added in version 3, audited, read cold», lines 3–6 (md l. 1117). Replace «Version 2 added the strictness of the cuts to the (Cut) of Theorem 7.8 and restated Lemma 7.2(b); no other statement of a theorem changed in versions 2 to 6. In version 3, Lemma 7.9 was strengthened, Lemma 10.6(a) gained the hypothesis «even», and Lemma 10.10 gained the explicit quantifier «for every `L ≥ 0` and every floor `f`».» by «Version 2 added the strictness of the cuts to the (Cut) of Theorem 7.8 and restated Lemma 7.2(b); version 3 strengthened Lemma 7.9, added the hypothesis «even» to Lemma 10.6(a) and the explicit quantifier «for every `L ≥ 0` and every floor `f`» to Lemma 10.10; no other numbered statement changed in versions 2 to 6.»
  2. **E2** — p. 48, Acknowledgements, paragraph «The work took …», line 1 (md l. 1135). Replace «The work took four days, from 2 to 5 October 2026.» by «The work took five days, from 2 to 6 October 2026.»
  3. **E3** — p. 46, §12.2, second row on the page (reader 3, «Theorems D and 7.10 on the lattices `T(λ)`»), md l. 1095. The printed range `λ ≤ 63, i ≤ 8, α = 1, 2` has 1 134 cells and pooling acts in 218 of them, not «1 401 cells» and «274 cells». Fix: take the range that reader 3 actually ran from its log in the project's record and print it; if the log confirms the printed range, print «1 134 cells» and «218 cells» (and re-run that check if the log cannot say which cells passed).
  4. **D1** — p. 9, «Why «dance»», lines 4–5 (md l. 196). Replace «each move gives every new floor the payment minus half the product of the payments of two adjacent old floors» by «each move gives every new floor a payment equal to minus half the product of the payments of two adjacent old floors».

## 1. The changes of version 6 (§3.1, item by item)

### 1.1 The hunks of the diff (§3.1 item 1)

The word-level diff (`scratch/py/worddiff.py`, `logs/worddiff.log`) has 18 hunks. None changes a symbol, a number, a quantifier or a hypothesis of a numbered statement. Four touch a proof step, in wording only:

| hunk | where (v6 md line; pdf page) | numbered statement / proof step? | content changed? | verdict |
|---|---|---|---|---|
| 1 | header (6; p. 1) | no | date, version | HOLDS |
| 2 | §1.0 record (32; p. 2) | no | records reading 7 | HOLDS (see §5) |
| 3 | §1.7 «Why dance» (196; p. 9) | no (informal paragraph) | wording | **PRESENTATION D1** (below) |
| 4 | proof of Prop. 4.1 (368; p. 16) | proof step | no: «(one for each `n` and `s'`)» added | HOLDS |
| 5 | proof of Prop. 9.6 (H) (746; p. 30) | proof step | no: «the child» → `fit(x_{H'})` | HOLDS (one inherited «its», taste list) |
| 6 | §10.1, definition of `X̄` (796; p. 33) | display before Cor. 10.2 | `exp F` → `exp(F)` | HOLDS |
| 7 | §10.2 (811; p. 33) | no | `cosh u` → `cosh(u)` | HOLDS |
| 8 | proof of Lemma 10.11 (914; p. 37) | proof step | «by subadditivity» moved to the inequality it justifies | HOLDS |
| 9 | proof of Lemma 10.19 (1002; p. 41) | proof step | `[½, 1]` → `[1/2, 1]`, now as in §10.2 (p. 34) | HOLDS |
| 10–12 | §12.2 cells (1100, 1102, 1112; pp. 46–47) | no | wording of cells | HOLDS (counts re-done, below) |
| 13–16 | §13, Appendix A (1116–1122, 1149–1150; pp. 48–50) | no | record | see §5: **ERROR E1** |
| 17–18 | references [IKKY23], [Yue24] (1169, 1185; pp. 51–52) | no | «Paper No.» | HOLDS |

### 1.2 The items of CORRECTIONS §1 and §2 (§3.1 item 2), md AND pdf

| item | md | pdf | wording exact? | verdict |
|---|---|---|---|---|
| R1 (§13 «no other statement of a theorem changed in versions 2 to 6») | done (l. 1117) | done (p. 48) | **no** — contradicted by the next sentence of the same bullet | **ERROR E1** (§5) |
| R2 (App. A, four counts) | done (l. 1149) | done (p. 50) | yes | HOLDS |
| R3 (§13 «read cold» / «made by the auditor, not yet read cold») | done (l. 1119–1120) | done (p. 48) | yes | HOLDS |
| «left as they are» list removed; the two false claims of v5 removed | done (l. 1149) | done (p. 50) | yes | HOLDS |
| §1.0, §13, App. A record reading 7, v6 not yet read cold | done | done (pp. 2, 48, 50) | yes | HOLDS |
| header «6 October 2026 · version 6» | done | done (p. 1) | yes | HOLDS |
| P2.4-a `fit(x_{H'})` (the house `H'` of Lemma 7.7), twice | done (l. 746) | done (p. 30) | yes: Lemma 7.7 defines `H' = (I', c, ℓ mod 2^c, α)`, and step 1 of Thm 7.8 does keep the level sets of `fit(x_{H'})` (Lemma 7.2(b), `d_1` changes only at strict cuts) | HOLDS |
| P2.4-b «Why dance» | done (l. 196) | done (p. 9) | the content is right for both moves (Prop. 4.1: `π'(f) = −π(2f)π(2f+1)/2`; Prop. 4.2: `−π(2f)π(2f+1)/2` and `−π(2f+1)π(2f+2)/2`, adjacent old floors; evenness: half a product of two even numbers), but the phrase «gives every new floor **the payment minus half the product** of the payments» reads naturally as a subtraction (old payment − ½·product), which is false | **PRESENTATION D1** |
| P2.2-a | done (l. 368) | done (p. 16) | yes | HOLDS |
| P2.2-b | done (l. 914) | done (p. 37) | yes | HOLDS |
| P2.6-a «the 7 634 cells of its row on the matrices `M`» | done (l. 1100) | done (p. 46) | yes: reader 4's row «Theorem 7.10 on the matrices `M`» has 7 874 cells; 7 874 − 240 = 7 634 = 7 620 + 14 | HOLDS |
| P2.6-b «none for Propositions 5.3 and 5.4, Lemma 7.5 and (H)» | done (l. 1102) | done (p. 47) | yes: the row's only control is for integrality, and the cell says so | HOLDS |
| P2.6-c «the 10 455 cells of the fifth reader's second row» | done (l. 1112) | done (p. 47) | yes: reader 5's second row of §12.2 is the one with 10 455 cells | HOLDS |
| P2.7-a «Paper No.» | done | done (pp. 51–52) | yes: [IKKY23], [LZ22], [Yue24] all «Paper No.» | HOLDS |
| PD16 `exp(F)`, `cosh(u)`, `L = [[1, 0], [1/2, 1]]` | done (no `exp F`, `cosh u` left; `½` remains only as the scalar `−½` in formulas of §4, which is not the object of PD16) | done (pp. 7, 33, 34, 41) | yes | HOLDS |

**D1 (PRESENTATION, counted).** p. 9, «Why «dance»», lines 4–5 of the paragraph (md l. 196). Fix: «each move gives every new floor **a payment equal to minus half the product** of the payments of two adjacent old floors».

### 1.3 The cells of §12 (7 634, 10 455, «none for …»)

Recounted by enumeration (`scratch/py/counts.py`, `logs/counts.log`, sealed S1, hit): λ from 1, `i` from 0, houses with `k ≥ 1`.
- Reader 4/6 range `λ ≤ 127, i ≤ 30, α = 1, 2`: 7 874 = 254 (`i = 0`) + 7 620 (`i ≥ 1`); of the 254, 240 have `I ≠ ∅` and 14 have `I = ∅`; 7 874 − 240 = 7 634. The cells of p. 46 and p. 47 agree with each other.
- Reader 5 range `λ ≤ 255, i ≤ 40`: 10 455 cells, 10 200 with `i ≥ 1`, 9 880 with `i ≥ 1` and `I ≠ ∅`.
- Houses `k ≤ 6, α ≤ 3`: 16 380; with `I ≠ ∅`: 16 002, and 3 × 16 002 = 48 006 house-checks; `k ≤ 7`: 65 532. Penalty shifts: 8 001 × 24 = 192 024 (24 = the pairs `(P_r, P_c) ∈ [0, 4]^2` other than `(0, 0)`).
- §12.1 row of Props 5.2–5.4: 14 560 clocks, 301 clocks (`D ≠ ∅`, `i = 0`), 109 200 entries; Theorem 7.10 row: 1 638 cells.
**Second recount, of the «pooling» cells and the integrality controls** (`scratch/py/pooling_counts.py`, my own code from the definitions of §1.2, §5, Prop. 5.4 and §7.3; `logs/pooling_counts.log`; sealed S5): 322 cells where pooling acts for `λ < 64, i ≤ 12, α = 1, 2` (§12.1) ✓; 1 876 for `λ ≤ 127, i ≤ 30, α = 1, 2` (reader 3) ✓, of which 1 834 with `i ≥ 1` (reader 4) ✓; 2 316 of 9 880 cells non-integral with `1` added at the first dancer (reader 5) ✓; 1 942 of 16 380 houses likewise ✓; no non-integral fit of `x_H` in the 65 532 houses with `k ≤ 7, α ≤ 3`, nor of the clocks of any cell above (Lemma 7.9) ✓.

**One row does not agree with its own range: E3.** §12.2, reader 3, «Theorems D and 7.10 on the lattices `T(λ)` | `λ ≤ 63, i ≤ 8, α = 1, 2` | 1 401 cells, 0 failures | the raw clocks are rejected in all 274 cells where pooling acts» (p. 46, second row on the page; md l. 1095). The printed range has 63 × 9 × 2 = 1 134 cells (64 × 9 × 2 = 1 152 with `λ = 0`), and pooling acts in 218 of them (161 with `α = 1`, 57 with `α = 2`; `logs/explore_d.log`). 1 401 is odd, so it is not a count over `α = 1, 2` of any rectangle of `(λ, i)`; and 274 > 218, so the reader's cells reach outside the printed range. The same code reproduces six other counts of §12 exactly, so I take the row as wrong as printed: either its range or its two numbers. See §6 for what the earlier reading and the gates say.

No other row says more than a check of its kind can show: the finite rows state finite ranges, the measurement rows (§10.5 Remark (2), the turned lid) are called measurements, and the rows with no control say «none». **HOLDS.**

### 1.4 The record sentences (§3.1 item 3)
See §5. Summary: §1.0 and Appendix A are exact; §13 bullet 2 is false (E1); the Acknowledgements sentence «The work took four days, from 2 to 5 October 2026» is false for a text dated 6 October whose seventh reading and version 6 are of 6 October (E2). Nothing is said to be left undone or half done; §13 «Not done» lists only future work (the cold reading of v6, a referee, a formal verification), which is honest.

## 2. The whole pdf, read for correctness (§3.2; the page list is in `checks/PAGES.md`)

### 2.1 Every page (§3.2 item 1)
52 of 52 pages looked at, in order, at 90 dpi; doubtful regions at 200 dpi (and one at 400 dpi) on pp. 2, 4, 5, 6, 13, 16, 34, 35, 36, 41, 42. One line per page in `checks/PAGES.md`. **No page looks broken.** Pages 25 and 43 end short before a new section (§7.4, §12): not a defect by §1.

### 2.2 The text, read as a reader (§3.2 item 2)
I read the md of version 6 whole, line by line (1–1185), and the pdf page by page. I did not re-prove every theorem; I followed every statement, definition and proof step, and re-did by hand the following, all of which **hold**:
- the examples: `n = 6` (every raw clock, the pooled `6, 6`, the total `{1: 12, 2: 4, 3: 1, 5: 4, 6: 10}`: 31 = 2^5 − 1 factors and exponent 103 = 57 + 15 + 30 + 1 = `v_2` of the tree count); `n = 5` (`{1: 6, 3: 4, 4: 1, 6: 4}`: 15 factors, exponent 46; halving gives `{2: 4, 3: 1, 5: 4}`, `a_5 = 6`); `n = 3` (`{1: 1, 3: 2}`); Cor. 1.7 for `e = 1, 2` (exponent 19 for `Q_4`);
- the matrix of the example after Thm D (all ten entries from Thm 4.4 and `q_2 = 1 + 2y_0 − y_1 − y_0y_1`);
- the recursion `c^{(h+1)}` in the proof of Thm 4.4; the subadditivity identity after Lemma 4.5; the bound `2^{|I|} ≤ ⌊λ/2⌋ + 1`;
- Prop. 3.1(a) (`[E, F]` on `b_1 n`), Prop. 5.3 step 1, Lemma 6.4 (both cases), Thm 6.2 (both cases), the counterexample of Lemma 7.2(b) (`(5, 4, 4, 3)` against `(5, 5, 3, 3)`), the antisymmetry rule of §7.1, step 2 and step 3(a) of Thm 7.8, the data of the houses `(I, k, 0, 1)` and `(I, k, K − 1, 1)` in Props 9.3–9.4, Lemma 9.5, step (K) of Prop. 9.6, Lemma 9.7 at `n = 5, 6`, the proof of Cor. 1.6 (`n = 4`, the three particular cases), Lemma 9.9 / Thm 9.10 (`v_2(i) = t_1 − 1`);
- §10: `η_1 = 1`, `η'_1 = 1/3` and the general `η_m` from `u·tanh(u/2)`; `π'(f) = −4(c + f)u_f` in Lemma 10.4(b); the shift invariance of `Θ` (Lemma 10.13(b)); the `F`-coefficient `η(4y − 2 ± 1)` and the payment `2χ(2y)`, `χ = X^2 ± X`, in Cor. 10.21; the payments `4y`, `4(y + [i even])` in Thm 10.22; the count 62 × 4 = 248, 2 × 248 = 496 of Remark (2); the mod-2 layer `rank = a_n` (§1.3 and §10.8 agree).

I found **no false mathematical statement, no step that does not follow and no object used before it is defined.** The one defect of wording is D1 (§1 of this report). The ambiguity of «its value» in Prop. 9.6 (H) is in the taste list.

### 2.3 Things that look broken (§3.2 item 5)
None found: no formula split so that it reads wrongly, no symbol missing or boxed (`□` occurs 4 times, and it is the box product `Q_a □ C_b` of the md, §11), no script detached, no table cut or overflowing, no word past the margin seen, no heading alone at a foot, no label separated from its statement. The numbered steps 1–8 of the proof of Thm 7.8 are all printed (pp. 26–27), with (Cut) cases (a)–(d) and the five cases of step 8.

### 2.4 Fonts and metadata (§3.2 item 6)
`pdfinfo`: Title «The Dancing Sand Theorem», Subject the subtitle, Author «Rafael Amichis Luengo», 52 pages, A4, md5 `f0ebd590af2e47d1406f9cc7c6145c4d` (= CORRECTIONS). `pdffonts`: every font embedded (`emb yes`), Type 3 STIX Two Text/Math and two CID TrueType Menlo subsets; no U+FFFD in the text layer. **HOLDS.** (Type 3 fonts are not a defect by §1.)

## 3. md against pdf, cross-references, citations (§3.2 items 3–4)

### 3.1 md against pdf
My own scripts, not the author's:
- **Prose words** (`scratch/py/mdpdf3.py`, `logs/mdpdf3.log`): 18 829 md words against 18 842 pdf words; 57 differences, every one an artefact of the extraction, inspected one by one: hyphen joins («non-increasing» / «nonincreasing»), possessive apostrophes, the repeated table headers of §1.7 and §12, and words that the text layer lists in another order around displays and two-column formulas. **No word lost, added or changed.** The first versions of the script (`mdpdf.py`, `mdpdf2.py`) failed on formula words and are kept as the record of the method.
- **Numbers** (`scratch/py/mdpdfnum.py`, `logs/mdpdfnum.log`): every number of three or more digits, in order: §12 105 = 105, identical; §1.0–§1.4 7 = 7; §13 and App. A 15 = 15 (the pdf pages also hold the end of §12 and the start of the references).
- **Statements, list numbers, bold labels**: read on the page against the md. Every theorem, lemma, proposition and corollary label is printed with its text; the numbered lists (§1.5 1–5, §1.8 1–5, proof of Thm 7.8 1–8, proof of Cor. 1.6 1–4, §11 1–6) are complete. The bold of the md is kept on every label and every bold span that begins with a word; a bold span that begins with a formula is set as plain math (displays, and the two bullets of Cor. 1.6): taste list.
**HOLDS.**

### 3.2 Cross-references
`scratch/py/myxrefs.py` (`logs/myxrefs.log`): 72 numbered items defined, 55 sections. Every internal «Lemma / Theorem / Proposition / Corollary x.y» and every «§x.y» resolves. The check can fail: it flagged exactly the five external references (Gao et al.'s Theorems 4.1, 4.2 and Proposition 2.5, [Hum72, §26], [CSX17, §5.2]), which are not items of this paper. Read for meaning, the references I followed say what is claimed (e.g. Remark (1) after Thm 3.6, Prop. 3.1(c), Lemma 5.1(b), Lemma 7.2(c), step 1 of Thm 7.8, Lemma 10.13(c), Lemma 10.14(c), Remark (2) of §10.5, Prop. 9.6 (H), the row of §12.2 for Larsen). **HOLDS.**

### 3.3 Citations and references
- 32 reference keys; every key is cited, every cited key is in the list.
- The nine quotations (Bai p. 253; [DJ14]; [CSX17, §5.2]; [IKKY23, §7]; [GMMY24] twice; [MGM19]; [Aky26, §4] twice) are verbatim in the sources (`scratch/py/quotes.py`, `logs/quotes.log`); two altered quotations are reported missing (`logs/cites.log`), so the check can fail. The «[sic]» of [IKKY23] marks «the just» of the source.
- Numbered items cited, checked in the sources: [Bai03] Thms 1.1, 1.2, 1.3, Lemma 2.2, Cor. 2.3 (2^{n−1} ones in the Smith form); [GMMY24] Thms 4.1 (`n ≥ 2`), 4.2 (`n ≥ 3`), Conj. 4.14 (the formula of Cor. 1.6), Conj. 5.4, Props 1.9, 2.12 (rank `2^{r−1} − 2^{⌊(r−1)/2⌋}`, so `r = n − 1`), 2.5 (proof: `u_i := x_i − 1`), Remarks 2.13 and 4.4, Table 1 («table from [2]», i.e. Bai), §2.2 (non-generic, codimension one); [IKKY23] Prop. 37; [CSX17] §5 (5) and §5.2; [Lar24] §2 (fusion graph); [Aky26] §4 «Further directions». All **HOLD**.
- Titles, authors and arXiv numbers of the 14 references with a source: exact (the arXiv numbers match the headers of the sources). Journal volumes and pages ([GMMY24], [IKKY23], [Yue24], [DHS18], [CSX17], [DJ14], [LZ22], [RT14]): not in the arXiv texts given; **not verified** (§10). The other references (books, 19th-century papers, [EL91], [OEIS]) have no source here: not verified.

## 4. The acceptance list and its controls (§3.3)

Read before running: `acceptance.py` and `fill.py`, `loose.py`, `xrefs.py`, `md_vs_pdf.py` (it calls these four; `margins.py` and `glyphs.py` are in the folder but not called, and `glyphs.py` reads a fixed path of another folder). Runs, all `VIGIA-FIN-OK`: `logs/acc_v6.log`, `logs/acc_v6_control.log`, `logs/acc_v5.log`, with `TMPDIR` in `scratch/tmp`.

| check | v6 | control mode on v6 | v5 | does it measure its name? can its control fail? | my verdict |
|---|---|---|---|---|---|
| 1 list numbers | PASS | **PASS** (control dead) | FAIL: «2. (Λ).», «3. (Cut).» | yes, for items at the start of a line beginning with a letter, «(» or «Λ» (an item beginning with a formula is skipped). The built-in damage `raw.replace('2. (Λ).', …)` never acts, because `pdftotext -raw` prints «2.(Λ).»; the v5 run is the only working control | HOLDS on v6 (and I saw 1–8 on pp. 26–27) |
| 2 md words | PASS (14 458 words) | FAIL | PASS | counts, not order; a prose word lost from the pdf can be masked by the same word inside a formula (e.g. «max», «mod»), since formula words are dropped from the md but kept in the pdf. Control fires | HOLDS on v6; my ordered comparison (§3.1) found no word lost |
| 3 margins | PASS (edge 542 pt, 0 beyond) | FAIL | PASS | yes. Control fires | HOLDS |
| 4 widows | PASS | **PASS** (control dead) | FAIL: p. 20 | a short last line at a page top, starting at the left margin, ending in «.:;» or ∎. The built-in fake widow is put at y = 100 pt, below the real first line (y ≈ 54–64 pt), so it never fires; the v5 run is the working control. An indented short line (a list item) is not caught (v5 p. 22 shows one). The statement-label exception acts on v6 only on p. 39 («Lemma 10.14. (a) `𝒯_h` is a ring.», a statement beginning, not a widow: looked at) | HOLDS on v6 |
| 5 page fill | PASS | PASS (input not damaged) | PASS | yes; **no control can fail in any run shown** (fill.py re-reads the undamaged bbox file). Exception «page before a new section»: v6 pp. 25 (77.9 %, before §7.4) and 43 (81.1 %, before §12), looked at: genuine; v5 p. 44 (83.8 %, before §12.2), looked at (`scratch/png/v5p-44.png`): genuine. The regex `\d+(\.\d+)*\.? [A-Z]` would also accept a numbered list item («1. Nothing …») at the top of the next page as a «section»; it does not happen here | measure without control; the pages are right by my eye |
| 6 loose lines | PASS | PASS (input not damaged) | PASS | yes; no control in any run. The three `NOT_TEXT` positions, looked at: p. 11 y = 228 is the display (K) with its limits; p. 9 y = 276 is a three-cell row of the §1.7 table; p. 35 y = 482 is the inline block matrix with `G^{10}, G^{11}, G^{00}, G^{01}`. None hides a loose text line. 14 text lines at 2×–2.6×: not a defect by §1 | measure without control; nothing hidden |
| 7 fonts and glyphs | PASS (126 fonts, 0 not embedded, 0 missing) | FAIL | PASS | yes (`split()[-5]` is the `emb` column). Control fires | HOLDS |
| 8 hyphenation | PASS; 60 breaks listed, all read by me: all right | PASS (no hyphen damaged) | FAIL: the three of reading 7 | yes; the v5 run is its control | HOLDS |
| 9 xrefs and statements | «PASS» (never judged) | — | — | **its output is cut** (`[-8:]` and `[-15:]`), against «every check prints its whole output, nothing cut». Run whole (`logs/mdvspdf_full.log`): `xrefs.py` prints 19 «MISSING TARGET» lines that check 9 hid, all false positives (it does not see labels set in a blockquote `> **Theorem D.**`, nor the lettered labels Theorem D/O/F/U/DW, Lemma W/K, nor external items like [Bai03, Theorem 1.2]); so it never checked the references to Theorem D, Corollaries 1.4–1.7, etc. `md_vs_pdf.py` reports the §1.0 and §12.1 tables «NOT a subsequence» (multiset OK): an artefact of the order in which pdftotext reads table cells and scripts; my ordered comparison of every number of three or more digits gives 105 = 105 in §12 | the paper is right (my §3.2–§3.3); the check is weaker than CORRECTIONS §4 says |

**Findings on the list (about the tool, not the paper):**
- A1. MISSION §3.3 expects «every check but 9 must FAIL» in control mode. Only checks 2, 3, 7 fire; the built-in damages for 1 and 4 are dead, and 5, 6, 8 receive no damage. CORRECTIONS §4 is consistent with this (its control column names the v5 run for 1, 4, 8 and gives no failing control for 5, 6), so it says nothing false; but the `control` mode does not do what its docstring says («every check must FAIL»).
- A2. CORRECTIONS §4, check 9, «0 missing internal targets»: true only of the last eight lines that check 9 shows. The uncut `xrefs.py` output has 19 false «missing» targets, and the references to every statement set in a blockquote were never checked by it. My own check (§3.2) resolves them all.
- A3. CORRECTIONS §4, «Every check prints its whole output, nothing cut»: false for check 9.
None of A1–A3 is a defect of the pdf; none hides one (I checked each object by other means).

## 5. The mathematics of the record (§3.4)

Every sentence of §1.0, §13 and Appendix A that says what a version changed or what a reading found, checked against the text of version 6 and against the diff:

| sentence | checked against | verdict |
|---|---|---|
| §1.0 / App. A: v1's gap was the integer part of Lemma 7.2(b), «false as stated», used by four proofs (Thm 7.8 step 1, Lemma 7.9, Thm 7.10, Prop. 9.6); no theorem affected | Lemma 7.2(b) now carries the hypothesis «integer and constant on every level set» and its proof gives the counterexample `x = (3, 4, 3, 4)`, `δ = (1, 1, 0, 0)` (re-computed: right); the four proofs now cite strict cuts or Lemma 7.9 | HOLDS |
| §1.0: «Version 2 repaired it (§7.1, §7.4, §9.2)» | Lemma 7.2(b) is in §7.1, the strict (Cut) in §7.4, Prop. 9.6 in §9.2; the uses in §7.5 (Lemma 7.9, Thm 7.10) are not in the parenthesis, but App. A says «cites it at each use» | HOLDS (taste: §7.5 could be added) |
| §1.0 / App. A: reader 4 found a false sentence in Remark (2) of §10.5 («every payment system»), and the same missing word in Lemma 10.6(a) | Remark (2) now says «every even payment system dances clean»; Lemma 10.6(a) says «For an even payment system» | HOLDS |
| §13: «Version 2 added the strictness of the cuts to the (Cut) of Theorem 7.8 and restated Lemma 7.2(b)» | Thm 7.8 (Cut): «these cuts are **strict**»; Lemma 7.2(b): restated with the integer hypothesis | HOLDS |
| §13: «… **no other statement of a theorem changed in versions 2 to 6.** In version 3, Lemma 7.9 was strengthened, Lemma 10.6(a) gained the hypothesis «even», and Lemma 10.10 gained the explicit quantifier …» | The same bullet, the next sentence: three more statements changed in version 3 (and Lemma 7.9 in its new form is a new statement, §13 bullet 2 itself and §12.2 «Lemma 7.9 of version 2»). The sentence counts Lemma 7.2(b) as a «statement of a theorem», so a lemma is one; then «no other … changed» is false. This is the sentence the seventh reading found false (App. A), corrected only for Thm 7.8 | **ERROR E1** |
| §13: v4 «audited, read cold», v5 «read cold», v6 «made by the auditor, not yet read cold»; «No mathematical statement changed» for v4, v5, v6 | App. A bullets; for v6 the diff (no hunk changes a statement: §1.1 of this report). For v4 and v5 I have no v3/v4 text: not verifiable beyond agreement with App. A | HOLDS (v6); consistent (v4, v5) |
| App. A, v5: «No mathematical statement changed, and no number; the descriptions of four counts of §12 were made exact (the 7 634 cells, the 301 clocks, the 192 024 cells, the 9 880 cells)» | the four descriptions are present in v6 §12 and right (my recount, §1.3); v4 not given | consistent, not fully verifiable |
| App. A, v5: reading 7 found «one false sentence in this record (§13 said that no statement of a theorem had changed in versions 2 to 5 …)» | the v5 md, l. 1117: «No statement of a theorem changed in versions 2, 3, 4 or 5. Lemma 7.2(b) was restated in version 2.» | HOLDS |
| App. A, v6: «makes those corrections. No mathematical statement changed. Its changes have not yet been read cold.» | the diff; CORRECTIONS §1–§2 | HOLDS |
| §13 «Not done: a cold reading of the changes of version 6; a human referee; a formal verification.» | nothing is said to be left half done; the «left as they are» list of v5 is gone (diff hunk 16) | HOLDS |
| Acknowledgements: «**The work took four days, from 2 to 5 October 2026.**» | the header (6 October 2026), App. A (reading 7 «on 6 October 2026», version 6 made after it) | **ERROR E2** |

**E1 (ERROR, record; on the narrow reading «theorem» = only the items labelled Theorem it would be an inexact sentence, but the same sentence puts Lemma 7.2(b) before «no other», so the natural reading is the generic one).** p. 48, §13, bullet «Added in version 3, audited, read cold», lines 3–5 (md l. 1117). Fix: «Version 2 added the strictness of the cuts to the (Cut) of Theorem 7.8 and restated Lemma 7.2(b); version 3 strengthened Lemma 7.9, added the hypothesis «even» to Lemma 10.6(a) and the explicit quantifier «for every `L ≥ 0` and every floor `f`» to Lemma 10.10; no other numbered statement changed in versions 2 to 6.» (and delete the following sentence «In version 3, …», now included).

**E2 (ERROR, record).** p. 48, Acknowledgements, 4th paragraph, line 1 (md l. 1135). Fix: «The work took five days, from 2 to 6 October 2026.» (or: «The mathematics took four days, from 2 to 5 October 2026; the cold readings of the text went on to 6 October.»)

No mathematical statement of the paper is affected by E1 or E2.

## 6. After everything else (§5)

Opened only after §1–§5 of this report were written (`logs/DIARY.md`, entry «opening material/read_after/ now»). Read whole: `REPORT_COLD_7.md`, `checks/PDF_DEFECTS_7.md`, `CALIFICACION_LECTOR_FRIO_7_v1.md`, `ESTRATEGIA_PDF_A_LA_PRIMERA_v1.md`; of the builder, `text_edits.py` (grep of the edits behind my findings) and the file list; the gates were not run (below).

### 6.1 The defects of reading 7 in version 6 (judged on the v6 pages, by the standard of §1)

| defect (reading 7) | in v6 | v6 page / evidence |
|---|---|---|
| PD1 step numbers 2, 3 of Thm 7.8 lost | **fixed** | pp. 26–27, 1–8 printed; check 1 |
| PD2 short pages 13, 18, 44 | fixed / not a defect by §1 | only pp. 25 and 43 are under 85 %, each before a new section |
| PD3 widows pp. 20, 37 | **fixed** | check 4; by eye on every page |
| PD4 display runs split pp. 12/13, 24/25 | **fixed** | the grids of p. 13 and p. 25 are whole |
| PD5 formula broken at «=» across a page turn | not fixed; **not a defect by §1** (a break after a relation that TeX allows) | p. 14/15: «V ⊗ T(2l + 1) = V ⊗ Φ(T(l)) =» / «T(2l + 2) by definition» |
| PD6 conclusion of Thm 10.15 run into (b) | **fixed** | p. 39 |
| PD7 bold of the md lost | **fixed** | p. 5 (naming trap, zoomed), p. 39 |
| PD8 case condition off its baseline | **fixed** | p. 17 (zoomed) |
| PD9 limits touching / off axis | fixed where I zoomed | pp. 4, 17, 41; legible everywhere |
| PD10 delimiters smaller than the fraction | **fixed** | p. 41 |
| PD11 holes in displays | not fixed; not a defect by §1 (spacing, the formula reads right) | p. 4 (Main Theorem ⊕), p. 18 (`c^{(h+1)}`) |
| PD12 scripts touching | fixed | p. 17 (zoomed) |
| PD13 ℓ with text side bearings | **fixed** | p. 24 (zoomed) |
| PD14 spacing glitches | fixed | p. 21 `R^♯(D)` (zoomed), p. 41 `in = in_k`, p. 43 □ |
| PD15 inline matrices / scripts too small | fixed for the matrices (pp. 34, 35, 41, 42, zoomed); `X^ι` on p. 11 is a correct small superscript ι that looks like a prime at reading size: taste list | p. 11 at 400 dpi |
| PD16 one object two ways | **fixed** | pp. 7, 33, 34, 41 |
| PD17 runs not aligned | not a defect by §1 | — |
| PD18 light math in bold headings | not a defect by §1 | — |
| PD19 short formula / bracket group broken | fixed at p. 38 («(a/2 + 2(χ/2)(2y))» whole); the other breaks are breaks TeX allows: not a defect by §1 | p. 38 |
| PD20 breaks after relations | not a defect by §1 | — |
| PD21 wrong hyphenation | **fixed** | check 8; all 60 breaks read |
| PD22 citations broken inside | not a defect by §1 (and App. A no longer claims otherwise) | — |
| PD23 numbers, initials cut | **fixed** | p. 2 «version 6.», p. 44 «48 006 house-checks», p. 46 «777 240 non-zero», pp. 50–51 «N. Terekhov», «Paper No. e11», «Mathematics 9», «Pure Math. 9» |
| PD24 a word alone before a display | not a defect by §1 | p. 37 «of» ends a full line |
| PD25 loose lines | not a defect by §1 | 14 lines at 2–2.6×, none at 3× |
| PD26 title page, p. 5 | not a defect by §1 | — |
| PD27 table design | not a defect by §1 | — |
| PD28 Type 3 fonts | not a defect by §1 | all embedded |
| R1 §13 «no statement of a theorem changed» | **not fixed: rewritten, still false** | p. 48, my **E1** |
| R2 App. A, four counts | **fixed** | p. 50 |
| R3 «audited» → «made by the auditor» | **fixed** | p. 48 |
| 2.5-bis «left as they are» incomplete | **fixed** (list removed, with the false claims) | p. 50 |
| P2.4-a «the child» | **fixed** | p. 30 |
| P2.4-b «Why dance» | fixed in content; the new wording reads as a subtraction | p. 9, my **D1** |
| P2.2-a, P2.2-b | **fixed** | pp. 16, 37 |
| P2.6-a, P2.6-b, P2.6-c | **fixed** | pp. 46–47 |
| P2.7-a «Paper No.» | **fixed** | pp. 51–52 |
| P2.7-b [TW21] arXiv number; [LZ22] appendix by S. Casalaina-Martin | not fixed; [TW21]: an absent arXiv number is not wrong; [LZ22]: the source's first page says «an appendix by Sebastian Casalaina-Martin» and its table of contents lists «Appendix A. The algebraic Abel–Prym map (by Sebastian Casalaina-Martin)»; the reference [LZ22] omits it — incomplete, not false: taste list | p. 51 |

Reading 7 found every one of my findings? No: it did not see E2 (the four days, then true of a text dated 5 October), nor E3 (the 1 401 / 274 row was in v5 unchanged), nor D1 (new in v6).

### 6.2 The builder: which rule caused each of my defects
All four defects are in the md, not made by the builder:
- **D1** is the replacement of `text_edits.py` l. 40 («each move gives every new floor the payment minus half the product …»), the author's fix of P2.4-b. Reading 7's proposed fix said «replaces the payment of each new floor by minus half the product …», which is unambiguous.
- **E1** is the replacement of `text_edits.py` l. 19 («Version 2 added … ; no other statement of a theorem changed in versions 2 to 6.»), placed before an unchanged sentence listing the three lemmas of version 3.
- **E2** is an unchanged sentence (Acknowledgements) that became false when version 6 recorded the work of 6 October.
- **E3** is an unchanged row of §12.2.
No builder rule is missing for them; what is missing is a check of the record against itself (dates and «no other … changed»), which no machine list of §4 of the strategy covers.

### 6.3 ESTRATEGIA: did version 6 do what its §4 and §6 say?
- §4.1 the fixed list: written and run (9 checks); but «each check prints its whole output, never cut» is not kept by check 9 (A3), and «md = pdf, every word and number» is only a count of words (check 2) and a tables-only number check that is never judged (check 9).
- §4.3 «every one of my checks gets a control that must fail»: **not done** for checks 5 and 6 (no control fires in any run) and the built-in controls of checks 1 and 4 are dead (A1); 1, 4, 8 are controlled only by the v5 run. §6's «Its controls fire on version 5 and on damaged inputs» is true of 1, 2, 3, 4, 7, 8, not of 5, 6.
- §4.4 regression check of the whole pdf text: no evidence given to me; my own md/pdf comparison (§3.1) shows no loss.
- §6 «Version 6 passes 9 of 9» — reproduced (S2). «Every page was looked at» — I did the same; I agree that no page is broken.
- §5 R1: the strategy's proposed wording («No statement of a theorem changed in versions 2–5, except that version 2 added the strictness …») was not the one used; the one used makes the clash with the next sentence (E1).
Verdict: option B did what it set out to do for the page (PD1 and the M kinds that matter are fixed); the text edits introduced D1 and kept E1.

### 6.4 The gates
The only row of §12 that made me doubt is reader 3's (E3); its code is not among the gates of the paper (`gates_of_the_paper/` holds the author's gates of §12.1), so no gate can settle it. My own recount reproduced every other count I tried (six with the same code). No gate run.

## 7. Doubtful, my taste (not counted)

- p. 30, Prop. 9.6 (H): «The first level set of the first half is the first level set of fit(`x_{H'}`) if its value is positive» — «its value» means the value of `Z_1 = fit(x_{H'}) + d_1` there, not of `fit(x_{H'})`; the next clause («otherwise `Z_1 ≤ 0` …») makes it clear. Inherited from v5.
- pp. 34, 35: the comma after a display matrix (`glue(X, Y) := [[…]],` and `[[x, 0], [x', x^+]],`) sits at the top right of the bracket, where a prime would sit.
- p. 11: the contravariant dual `X^ι` is a correct superscript ι that looks like a prime at reading size (its definition is on the same line).
- p. 6: the md bolds the bullets «`c_n = …` for `n ≥ 3`» and «`c_{n+1} = …` for `n ≥ 4`» of Cor. 1.6; the pdf does not (a bold span starting with a formula is plain throughout, displays included).
- p. 2, §1.0: «Version 2 repaired it (§7.1, §7.4, §9.2)» could add §7.5 (Lemma 7.9 and Thm 7.10 also cite the repair).
- p. 51, [LZ22]: «with an appendix by S. Casalaina-Martin» is missing (the source's own Appendix A is his).
- p. 46, reader 3's «all houses with `k ≤ 7`, `α = 1, 2`: 43 690 houses» = 2 · Σ_{k=0}^{7} 4^k counts the three degenerate houses with `k = 0`, while «every house with `k ≤ 7`, `α ≤ 3` (65 532)» = 3 · Σ_{k=1}^{7} 4^k leaves them out although §7.3 allows `k = 0`. Degenerate one-dancer houses; nothing claimed depends on them.
- p. 42: the subscript minus of `W_−` before `M_w(…)` in the display of Thm 10.22 looks like an underscore («W_M_w»).

## 8. Sealed predictions, hits and failures

All in `checks/SEALED.md`, each written before its run (times in `logs/DIARY.md`). **11 predictions: 9 hits, 2 failures.**
- Hits: S1 (17 pure counts of §12), S2 (acceptance on v6: 9 PASS), S4 (v5 fails exactly 1, 4, 8), S5(a) 322, S5(b) 1 876, S5(c) 1 834, S5(e) 2 316 of 9 880, S5(f) 1 942 of 16 380, S5(g) no non-integral fit.
- **Failures:** **S3**, half: I predicted that checks 5, 6, 8 pass in control mode (right) and that 1 and 4 fail (wrong: their built-in damages are dead, so only 3 of 8 controls fire). **S5(d)**: I gave 60 % to reproducing reader 3's 274; my count for the printed range is 218 — this failure is finding E3.

## 9. My errors

- M1. Two small inline `python3` runs outside the watchdog: the first page-grep of the pdf text (Part 2) and one text edit of this report (Part 2). Both light (seconds, MB); both noted in `logs/DIARY.md` at once; the page-grep was redone under the watchdog (`logs/find1.log`). Also two `cd` commands moved the shell into `scratch/` and `material/tools/` (nothing was written there).
- M2. My first two md/pdf word comparisons (`mdpdf.py`, `mdpdf2.py`) were noisy by design errors (formula words, primes); the third is the one I rely on.
- M3. I first listed [VZ24] among the references with journal data to verify; it has none (arXiv only). Corrected in §3.3.
- M4. S3 (above): I misjudged two of the dead controls.
- M5. The parenthesis on the narrow reading of E1 (§5) was added after I read reading 7's report, which read «theorem» narrowly. My verdict ERROR was written before, and stands; the note is there so that the reader can judge both readings.
- M6. A first 400 dpi zoom of p. 11 was cropped at the wrong height (harmless; redone).

## 10. What I did not read

- **Mathematics:** I read every statement, definition and proof step and re-did the computations listed in §2.2, but I did not re-prove every theorem. The long proofs of §10 (Lemmas 10.6, 10.8, 10.18–10.20, Thms 10.15, 10.16, 10.22) I followed step by step without re-deriving each identity; Thm 3.6, Lemma 3.5 and Prop. 3.1(d) likewise.
- **The v5 pdf:** only pp. 44–45 (to judge check 5); the v5 md served for the diff. **The v6 html:** not read.
- **References:** journal volumes and pages of the references whose source is an arXiv text, the books, the 19th-century papers, [EL91], [OEIS], [Kos66], [TW21]: not verified.
- **`read_after/`:** of the builder only `text_edits.py` (by grep) and the file names; `build_v6.sh`, `md2html_v6.py`, `phtml.py`, `pmath.py`, `chrome_pdf.sh`, `pdf_meta.py`, `builder_edits.py` not read. Of reading 7 not read: `checks/PAGES.md`, `checks/SEALED.md`, its `scratch/`. The gates: not read, not run.
- **E3:** reader 3's code and log are not in this folder, so I cannot say which of its range or its numbers is wrong.

## 11. Files with md5

Computed under the watchdog (`logs/md5_final.log`, VIGIA-FIN-OK); the list is `scratch/md5_final.txt` (`md5 -r`). Not in the table, because they change after it: `REPORT_COLD_8.md` itself (its md5 is on the last line of `logs/DIARY.md`), `logs/DIARY.md`, `ESTADO.md`, `logs/md5_final.log`, `scratch/md5_final.txt`. `logs/zoom.log` was rewritten at each zoom (it holds the last). The temporary folders of `acceptance.py` are in `scratch/tmp/`. Nothing was written outside this folder; nothing is in `scratch/_BORRAR/`.

| md5 | file |
|---|---|
| 1536ddccc61354144c510c382e4cb386 | checks/PAGES.md |
| 781957654af4febabf70f77178d3b9b3 | checks/PART1_NOTES.md |
| 2f3ac968a4105af7be1337573ca7be23 | checks/SEALED.md |
| 13d67f85b7994cc911efcbca49b09290 | scratch/py/check4_exc.py |
| aa10f27308d31897d52ba851b7d7a730 | scratch/py/cites.py |
| 35ae6a9e057b73eafa6fdcbff5804de2 | scratch/py/counts.py |
| 1ced7f9813cc98b8169c25462740278b | scratch/py/explore_d.py |
| 72ed60450944730b414836c2fec20fb8 | scratch/py/findpdf.py |
| d097077a552f47108ff91fc5ae5ec057 | scratch/py/mdpdf.py |
| 98e59e54d78a51aa6e3cffe1fb63a41b | scratch/py/mdpdf2.py |
| ccd7f7b11f5cdf189ff50ea3f2808b46 | scratch/py/mdpdf3.py |
| bc8a1cb586c309f063d2bc2339bf201f | scratch/py/mdpdfnum.py |
| 355f1c2718dc2f2ddad8e4a8fef6e432 | scratch/py/myxrefs.py |
| 2efe61a1b8d147fff93677a0e31ddc27 | scratch/py/pooling_counts.py |
| eab13574ca593724be376df6f79986ad | scratch/py/quotes.py |
| c4462efe3fea91a071202bc51dfc76c0 | scratch/py/worddiff.py |
| fc9c941cbfbb136cb99e5c8efb3dcbb5 | scratch/zoom.sh |
| 85bcca1a7b80afff25a631e22bd1e3d2 | scratch/v6_raw.txt |
| 9f5ae1da63ce8e08bbc43014645ec336 | scratch/v6_layout.txt |
| e7d73deaec46a5ab69132d64a5bed0d3 | scratch/v5_layout.txt |
| 24be4e2c94c725557de882035ace0079 | scratch/v6_rawmode.txt |
| 1caef9b4dde336f6832892b18373f4aa | scratch/v6_bbox.html |
| 6235bdce7ce6b069f920cb98ff4e73b7 | scratch/v5_bbox.html |
| f7c196926a728cfe7b84b30a781fdc3b | logs/acc_v5.log |
| d75c858f58f6313efd6ab6bde2fdbfdf | logs/acc_v6.log |
| bb4a9a8b9da429bb6bb1c08b161ee177 | logs/acc_v6_control.log |
| 2abb7b52505c25d2c44df5eb12838603 | logs/check4_exc.log |
| 91fb29bdaf25805e78cc5a70c0ad2615 | logs/cites.log |
| 73720d4abb03616d383576c7ee8a7c68 | logs/counts.log |
| f5fdefe726c8b243d09b544700a604fa | logs/explore_d.log |
| 2c02dbd6720082d414b548796806bf74 | logs/find1.log |
| cac79d7acb3fb03490fb9dd8ecbb9ba7 | logs/find2.log |
| 35ffc12fbc259414f67d43cf78f21b1d | logs/mdpdf.log |
| f60c2c94d5fa7c39644c5ddc2e91eddb | logs/mdpdf2.log |
| a863bab26df4be919cda8836357de3f2 | logs/mdpdf3.log |
| a829c4284b45a3a961c8390e160eb85d | logs/mdpdfnum.log |
| 5e21c7fe8102d005571dde3642d67c46 | logs/mdvspdf_full.log |
| 5f202481523b5c98cdcee716e442a711 | logs/myxrefs.log |
| a80b9dfb7f9efde04cb6a37a664756cd | logs/pdftext.log |
| a134d04ab34b15e71ff20fa430f1e227 | logs/pooling_counts.log |
| b8e1cd75f04ade48205ecb7084488625 | logs/quotes.log |
| 7c8d6268e64a40ddea8fba902370b0d5 | logs/r200_p2.log |
| 16ca5cad1de0b7edd3469a7260df1987 | logs/rawdiag.log |
| 3ed9d01a368994c4b1d1cbed83f1bf31 | logs/render90.log |
| b11c060c5c28e4c1594a000d07f6afaf | logs/v5p44.log |
| 4d87786657f7db37f3582a60240e7dde | logs/worddiff.log |
| b50789858433e408d390601f9c22f1ce | logs/zoom.log |
| bd41ce0383a0ed913d614739a3da6f91 | scratch/png/ — 54 page images (52 of v6 at 90 dpi, 2 of v5 at 60 dpi); md5 of the sorted `md5 -r` list |
| c82b9e9c3c1466f0dfe5b51a19c72d40 | scratch/png200/ — 19 crops at 200–400 dpi (same) |

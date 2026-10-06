# Corrections from version 4 to version 5 of «The Dancing Sand Theorem»

Grepy Muchas Pilas, 5 October 2026.

## Files

| file | md5 |
|---|---|
| `paper/THE_DANCING_SAND_THEOREM_v5.md` | `d805755691429f9438383007d2efd728` |
| `paper/THE_DANCING_SAND_THEOREM_v5.pdf` (51 pages, build 20) | `07e1e02a0b75ad3a6caf5a1f065eae61` |
| `paper/THE_DANCING_SAND_THEOREM_v5.html` | `6f38d5ac8b672967262afa9399769ebb` |

- **Builder.** Version 5 is built by `paper/build_v5.sh`. It runs, in order:
  - `paper/md2html_v5.py`, with rules (43)–(59) in its header;
  - `paper/phtml.py`, which sets the mathematics, with rules G9–G21 in its header;
  - `paper/chrome_pdf.sh`;
  - `paper/pdf_meta.py`.

  The phtml of version 4 is `paper/historico/phtml_v4.py`.
- **Version 4 moved.** Version 4 (md, html and pdf), `build_v4.sh` and `md2html_v4.py` are now in `paper/historico/`. Their md5 were checked before and after the move; they equal the md5 printed in `CORRECTIONS_v3_to_v4.md`.
- **Edits of the text.** Every edit is a script in `paper/v5_edits/`: `part1.py` to `part22.py`, with 111 checked replacements plus the conversion of the number sets in `part3`. `lib.py` checks that each replacement matches its text exactly once.
- **The source.** The source of every item below is cold reading 6:
  - its report, `reports/LECTOR_FRIO_6/delivered/REPORT_COLD_6.md` (md5 `98fa152e…`);
  - its defects, `checks/PDF_DEFECTS.md` (GD1–GD32) and `checks/PAGES.md` (page items);
  - our grading, `reports/LECTOR_FRIO_6/CALIFICACION_LECTOR_FRIO_6_v1.md`.
- **Checks.** The page checks are in `paper/checks_v5/`. They are the checks of version 4, but `fill.py` now ignores the page number in the bottom margin. Also run, unchanged: the reader's tools in `reports/LECTOR_FRIO_6/delivered/scratch/` (`pdfcheck.py`, `lines2.py`, `stmt_cmp.py` with its control, `xref2.py` with its control, `codenames.py`, `accents.py`, `apos.py`). The final logs, all ending `VIGIA-FIN-OK`, are:
  - `logs/build_v5_20.log`;
  - `logs/v5_allchecks_20.log`;
  - `logs/v5_readertools_20.log`;
  - `logs/v5_lines2_20.log`.
- **The gates.** The gates of §12 do not read the text. Their code is unchanged against `MANIFEST_md5.txt`.

**No mathematical statement changed.** The one number that changed is the description of the 7 634 cells of the fourth reader's row in §12.2 (item 1.1).

## 1. The record of the readings (report item 7, P-R1–P-R8; item 8; P-C1–P-C3) — `part1`, `part8`, `part21`, `part22`

1. **The 7 634 cells of the fourth reader's row (§12.2).** These are the 7 620 cells with `i ≥ 1` and the 14 cells with `i = 0` and `I = ∅`, where `M = 0`. The fourth reader's own log confirms it.
2. **§1.0.**
   - The gap is described: the integer part of Lemma 7.2(b) was false as stated, four proofs used it, and no theorem was affected.
   - Lemma 7.9 is described as «a two-line proof that the fit of every house is integral».
   - Version 4 is described as corrected «except two» defects.
   - The sixth reading and its verdict are added.
   - «The changes of version 5 have not yet been read cold.»
3. **§12.1.**
   - The row of Propositions 5.2 · 5.3 · 5.4 names what was checked: matrix entries, clocks and clocks, the last being the formula for `u_0(D)` with `D ≠ ∅`.
   - The row of Remark (2) gets the control «none».
4. **§12.2.**
   - «Six readers». The meanings of «none» and «fires» are stated.
   - Every «—» becomes «none».
   - The rows of the fifth reader say what the integrality control is and say that (H) and Lemma 7.5 have none.
   - A row for the sixth reader is added at the end of the table (`part8` moved it there from the middle).
5. **§13.**
   - Version 4 is read cold.
   - Version 5 is not.
   - «versions 2, 3, 4 or 5».
6. **Appendix A.**
   - Version 3 is no longer called «this text».
   - Version 3 printed three ranges of §12 wider or vaguer than the code ran.
   - Version 4 left two defects. Its parenthesis on the 7 634 cells was composed by the author and was wrong. The sixth reading is described.
   - A new bullet for version 5 states what was done and what was left as it is (§6 below).

## 2. Points of presentation (report items 3–6, 9; §2 H20; P-X1; p. 35 (b)) — `part2`

1. **P-T1, Proposition 9.6 (H).** The base cell now says why induction along step 1 of Theorem 7.8 keeps the level sets: `d_1` changes only at strict cuts.
2. **P-T2, Remark (2) of §10.5.** The citation is «proof of Lemma 10.6(a)».
3. **P-T3, §1.8 and §2.1.** The basis of Gao et al. is ours **up to the sign `(−1)^{|S|}`**.
4. **«Why dance».** A move «replaces the payments of two adjacent floors by minus half their product».
5. **Item 9.** The 2019 poster is by three of the four authors: [MGM19], Marx-Kuo, Gao and McDonald.
6. **P-X1.** The column «first use» of §1.6 is correct: `k_0` is removed and §2.2, §3.4, §4.4 and §1.2 are added where they belong.
7. **H20, p. 35 (b).** Parts (b) and (c) of the lemma on `𝒦`, and (b) of the proof of Lemma 10.6, stand on lines of their own.

## 3. Global typesetting defects GD1–GD32

| defect | what version 5 does | where |
|---|---|---|
| GD1 straight apostrophes | `’` in running text, a prime in formulas; the last one, after a code span, reworded | rule (43); `part18`; `apos.py`: 0 left |
| GD2 number sets in italic | ℤ, ℚ, 𝔽₂ in double-struck letters. Kept as letters, one by one: the variables `Z_1`, `Z_2`, the matrix `Z`, the sets `F_1`, `F_2`, the block `Q`, the cubes `Q_n` | `part3`, `part9` |
| GD3 accents off their letters | every accent is a box centred over its letter (bar, hat, tilde); precomposed letters are decomposed | G9 |
| GD4 fully ruled tables | horizontal rules only, text flush left, no shading | rule (50) |
| GD5, GD13 hyphenation | at least 3 letters before and 4 characters after a break; never inside a hyphenated compound | rule (44); `pdfcheck.py`: 74 hyphens, 0 flagged (its control: 3 of 3) |
| GD6 light digits in bold | «the whole 2-part» and «The mod-2 layer» set as text | `part4`, `part5` |
| GD7 shaded statements | no shading; the main statements keep a thin rule at the left (house style) | rule (50) |
| GD8 sentences that begin with a formula | 6 named by the reader and 19 more found by a search of the md (16 in `part13`, 3 in `part14`), all reworded. A statement right after its bold label («**Lemma 6.1.** `d̂_r ≥ T(r)`») is left as it is | `part4`, `part13`, `part14` |
| GD9, GD21 scripts | thin spaces after commas and around words in scripts; a condition with a comma under a big operator is stacked | G13 |
| GD10 baseline ellipsis | `⋯` between relations and binary operators | `part4` |
| GD11 bold mixed with formulas | a bold span that is mostly a formula is set light; Theorem 4.4's display in two lines without bold | rule (47); `part4` |
| GD12 the end-of-proof mark | ∎ from STIX Two Math at the right margin of the last line. In version 5 it never wraps alone: it is placed absolutely, and four no-break spaces glued to the last word keep its room (build 13 had left one alone at the top of p. 39) | rules (48), (59). Check: all 74 marks on a text line, at the right margin, at least 3 pt from the text |
| GD14 headings | `SL_2`, `𝔽_2`, `M` in headings set as mathematics | `part3` |
| GD15 conditions after displays | a quad | G18, rule (57) |
| GD16 small delimiters | brackets enlarged around sums and products with limits | G15 |
| GD17 ½ | a small stacked fraction | G16 |
| GD18 citations broken | a citation with a short locator never breaks. With a locator of more than 12 characters only «[Key,» is kept whole | rule (45) |
| GD19 «+» without spaces | fences counted per character | G11 |
| GD20 words in displays | word spaces next to short formulas, aligned grids for runs of displays | rules (51), (55) |
| GD22 labelled lists | no bullet | rule (52) |
| GD23 limits at the side | `max`, `min`, `mean`, `sup`, `inf` carry their limits under in displays | G12 |
| GD24 short formulas broken | no break inside a formula of at most 10 characters, inside a bracket group of at most 22, after a one-atom operand, after «⊗» (one pure tensor on one line, p. 16 (c)) | G19 |
| GD25 n-ary ⊕ | `⊕_λ` | `part4` |
| GD26 matrices as lists | matrices in brackets | G14; `part4` (row and column operations in words) |
| GD27 solidus before a big product | stacked fraction | G17 |
| GD28 «=:» split | one relation | G10 |
| GD29 numbers cut from nouns | a number is joined to the word after it | rule (46) |
| GD30 references | labels in a column; arXiv numbers for [DJ14], [RT14], [LZ22] | rule (53); `part6` |
| GD31 STIXGeneral fallbacks | ∇ and Δ of the filtrations set as formulas; no U+2060 (absent from STIX Two). `pdffonts`: only STIX Two Text, STIX Two Math and Menlo | `part7`; rule (12) |
| GD32 page numbers | a folio at the foot of every page but the first | rule (49) |

## 4. Page items (`checks/PAGES.md`)

The page items that are instances of a global defect are covered by §3. The specific ones were checked one by one on the pages of build 20:

- **p. 3 (b)** «o-order» is set with a non-breaking hyphen.
- **p. 7 (a)** «level h» does not wrap.
- **p. 7 (d)** The short page is gone: p. 7 is now 98 % full.
- **p. 11 (a)** The tag (K) is roman, at the right margin.
- **p. 12 (c), p. 25 (b)** The displays are aligned.
- **p. 17 (a)** Theorem 4.4's display is set in two lines, without bold.
- **p. 32 (d)** «Passing to `2·Syl_2 K(Q_n)` removes».
- **p. 34 (c)** «Dd» is one upright name.
- **p. 36 (a)** The window is kept on one line.
- **p. 36 (b)** There is a quad between the three formulas.
- **p. 37 (b)** `[F^{(m)} : m ≥ 1]` is kept whole.
- **p. 39 (b)** `l = 2, …, 63` is kept whole.
- **p. 42 (b)** No break after «2·».
- **p. 42 (c)** §12 now starts in the middle of p. 43, after §11.
- **p. 43 (c)** «⊕ coker» has a thin space.
- **p. 44 (a)** `{1: 6, …}` is kept together.
- **p. 44 (b)** «[Lar24, §2]» is kept together.
- **p. 46 (a)** «every b» is kept together.
- **p. 49 (b)** The volume and year of [EL91] are kept together.

The loose lines named on pp. 3–47 are treated in §5.

Left as they are:

- the break at «=» before the last formula of Lemma 2.4 («…= V =» / «Δ_A(1) = ∇_A(1)»), which TeX allows;
- the short last lines of paragraphs (the «runt» lines of p. 16, 17, 28, 29, 30). TeX keeps them as well, and the end-of-proof mark now never stands alone.

## 5. Loose lines (report §5 item 5) — `part10`–`part12`, `part15`–`part17`, `part19`, `part20`

Fourteen passages were reworded so that their lines are no longer loose; their content is the same. Measured with the reader's own `lines2.py` on build 20:

- the median word space is 3.31 pt;
- two lines reach twice the median, 6.9 and 7.1 pt;
- both carry a small matrix in the text (p. 33, proof of Lemma 10.4; p. 35, proof of Proposition 10.7). The measure counts the inner spaces of the matrix as word spaces, and on the page these lines read normally.

| check | version 4 | version 5 (build 20) |
|---|---|---|
| pages | 49 | 51 |
| statements of the md against the pdf (`stmt_cmp.py`) | — | every difference in the 27 of 75 statements it flags is an accent drawn as a separate mark, a prime `’`, or a stacked fraction (no letter or digit is missing); its control fires (28 of 75) |
| words past the right edge (`pdfcheck.py`) | 0 | 0 |
| words outside the text block (folios aside) | 0 | 0 |
| line-end hyphens flagged (`pdfcheck.py`) | 8 | 0 of 74 |
| ASCII apostrophes (`apos.py`) | 43 | 0 |
| cross-references unresolved (`xref2.py`) | 0 | 0 of 640; its control fires |
| code names broken (`codenames.py`) | 0 | 0 of 12 |
| lines at twice the median word space or more (`lines2.py`) | 6 (median 3.18 pt) | 2, both with a small matrix (median 3.31 pt) |
| lines with a gap above 6 pt / 7 pt (`gaps_text_words.py`) | 10 / 0 | 14 / 1. The one above 7 pt is the matrix line of p. 33. Formulas are now never broken inside, so more lines carry their spacing in the word gaps |
| pages under 90 % full (`fill.py`, the folio excluded) | p7 (84 %), p23 (89 %), p42 (75 %) | p1 (63 %: the title page, abstract only) and p5 (89 %: the heading of §1.4 and the boxed Corollary 1.5 go together to p. 6) |
| end-of-proof marks alone on a line | not measured | 0 of 74 |
| fonts (`pdffonts`) | STIX Two, STIXGeneral (GD12, GD31) | STIX Two Text, STIX Two Math, Menlo only |

## 6. What the record of version 5 says, and what was left

The Appendix A bullet for version 5 lists what was done. It also lists what was left as it is:

- the two matrix lines;
- statements that begin with a formula right after their bold label;
- the short last lines of paragraphs.

The §1.0 sentence says «corrected in this version 5 except as stated in Appendix A».

## 7. Builder rules added in version 5

- **`md2html_v5.py`:**
  - (43) apostrophes;
  - (44) hyphenation limits;
  - (45) citations;
  - (46) ties of numbers and short formulas;
  - (47) bold spans;
  - (48) and (59) the end-of-proof mark;
  - (49) page numbers;
  - (50) tables and statements;
  - (51) words in displays;
  - (52) labelled lists;
  - (53) reference labels;
  - (54) the display tag;
  - (55) aligned runs of displays;
  - (56) long tables;
  - (57) conditions after displays;
  - (58) the column «where».
- **`phtml.py`:**
  - G9 accents;
  - G10 «=:»;
  - G11 fences;
  - G12 limits under operator names;
  - G13 scripts;
  - G14 matrices;
  - G15 enlarged brackets;
  - G16 ½;
  - G17 stacked fractions;
  - G18 conditions;
  - G19 line breaking;
  - G20 «Dd» and spacing after operators;
  - G21 commas between formulas in displays.

The temporary switches used while measuring loose lines (`PH_*`, `MH_*` environment variables) were removed from both files before the final build; their final values are written into the code.

# Corrections from version 3 to version 4 of «The Dancing Sand Theorem»

Grepy Muchas Pilas, 5 October 2026.

## Files

| file | md5 |
|---|---|
| `paper/THE_DANCING_SAND_THEOREM_v4.md` | `e9ee10c433049ac3278e6ac3b9ca304e` |
| `paper/THE_DANCING_SAND_THEOREM_v4.pdf` (49 pages, build 27) | `c7becfae00581351690dc2c4c8ccf350` |
| `paper/THE_DANCING_SAND_THEOREM_v4.html` | `f7e02d1b5cade4a4a607b411cee61e5d` |

- The builder of version 4 is `paper/build_v4.sh`. It runs:
  - `paper/md2html_v4.py` (rules (27)–(42) in its header);
  - `paper/phtml.py`, which sets the mathematics in HTML;
  - `paper/chrome_pdf.sh` (Chrome headless, light flags);
  - `paper/pdf_meta.py`, which adds the author and the subject to the pdf.
- `paper/pmath.py` is the MathML translator. It was tried first and dropped (§3). `phtml.py` still imports its tokenizer and its tables of names.
- Version 3 (md, html, pdf), `build_v3.sh` and its builder `md2html.py` are now in `paper/historico/`; their md5 were checked before and after the move.
- Every edit of the text is a script in `paper/v4_edits/` (`part1.py` … `part13.py`, 51 replacements). `lib.py` checks that each replacement matches its text exactly the expected number of times.
- The page checks are in `paper/checks_v4/`:
  - our own: `fill.py`, `overflow.sh`, `loose2.py`, `allchecks.sh`;
  - copied unchanged from cold reader 5: `gaps_text_words.py`, `structure.py`, `widows.py`, `formula_lines.py`, `margins.py`, `md_vs_pdf.py`, `xrefs.py`.
- The final run is `logs/checks_v4_final_27.log` (VIGIA-FIN-OK).

**No mathematical statement changed, and no number changed** except the ranges of §12 that the fifth reader checked against the code (items 7, 8 and 11 below).

## 1. Source: cold reading 5, the text

The report is `reports/LECTOR_FRIO_5/REPORT_COLD_5.md`; its comparison with the history is `SECOND_LOOK_v1.md`.

1. **The reading record** (report §1.8; `part1` items 1, 9, 10). §1.0, §13 and Appendix A now say:
   - the changes of version 3 were read cold by the fifth reader, and they hold;
   - Lemma 7.9 is on the path of the printed proof of the Main Theorem;
   - the missing «even» in Lemma 10.6(a) was found by the author, not by reader 4;
   - the changes of version 4 have not yet been read cold.
2. **«The rounding never acts»** (report §1.3; `part1` item 2). §1.2 cites Lemma 7.9 together with Proposition 5.3, Lemma 7.5 and Proposition 5.4, and §8.
3. **The change of variables of [GMMY24]** (report §5 item 9; `part1` item 3). It is in the proof of Proposition 2.5, up to the sign `(−1)^{|S|}`.
4. **«Why dance»** (report §1.9; `part1` item 4). Only the first system pays `2^α(i + d)`. Each move multiplies two adjacent payments and halves them.
5. **Where strictness is used after Lemma 7.9** (report §1.2; `part1` item 5):
   - as written, in Theorem 7.8 (steps 1 and 3) and in Theorem 7.10;
   - with Lemma 7.9, a cut suffices there;
   - it is indispensable only in Proposition 9.6 (H), twice.
6. **The moves are clean, in the proof of Lemma 10.6(a)** (report §1.7; `part1` item 6). The proof now says why each move is clean, and cites Propositions 4.1 and 4.2.
7. **§12.1, the ranges of Propositions 5.2–5.4 and of Theorem 7.8** (report §1.10, §6; `part1` item 7). The value `λ ≤ 127` became `λ ≤ 126`, as in the code.
8. **§12.2, the cells of reader 4** (report §1.10; `part1` item 8):
   - the 7 634 cells are those with `i ≥ 1` (7 874 less the 240 with `i = 0`);
   - «Four readers» became «Five readers».
9. **References** (report §5 item 11; `part1` item 11):
   - [GMM19] became [MGM19], placed in alphabetical order;
   - [DEGJPP24] became [DEGJPP23];
   - the details of [GMMY24] and [Yue24] were reduced to what was verified;
   - [OEIS] now gives its access date.
10. **The fifth reader's gate in §12.2** (report §2, log `reports/LECTOR_FRIO_5/logs/gate_cold5_full.log`; `part2`, `part11`). Two rows were added, with every number taken from that log:
    - 65 532 houses, 192 024 penalty cells and 741 deletions, with the controls 1 942 of 16 380 and 7 967 of 30 078;
    - 10 455 real cells, with (H) on the 10 200 cells with `i ≥ 1`, and the control 2 316 of 9 880.

## 2. Source: cold reading 5, the pdf (report §4)

The report lists 8 global defects (G1–G8) and 28 specific ones (rows 1–28 of its table, §4 B).

- **G1–G8** (one italic font for formulas, flat scripts, bold formulas, no space between formulas of one display, slanted brackets, stretch inside formulas, italic words, upright `i` in italic labels). The mathematics is now set by `phtml.py`:
  - letters in Unicode mathematical italic;
  - digits, brackets, operators, operator names and words upright;
  - stacked scripts;
  - fixed operator spacing (relation 0.2778 em, binary 0.2222 em, punctuation 0.1667 em);
  - no bold and no stretch inside a formula.
  - Rules (27), (28), (35), (36).
- **Rows 6, 10, 13, 14, 23 (statements split across pages):** rule (31). The final `structure.py` finds no split statement; the four it cannot locate (Propositions 4.1 and 4.3, Lemmas 7.1 and 10.10) were checked by eye on pages 15, 16, 22 and 36.
- **Rows 2, 8, 9, 16, 18, 19, 22 (lines beginning with a relation or an operator; formulas broken across a page):** rules (29), (37), and `part3`, `part5`, `part8`. The word «every dancer is» was added in Corollary 1.6, item 1 (row 18).
- **Rows 4, 5 (displays wrapped by the renderer):** split by hand (`part3`, `part4`, `part12`; rule (37)).
- **Rows 11, 17 (an operator or a number separated from its word):** rules (29), (30), (32).
- **Rows 20, 21 (breaks between «]» and «[»):** the TeX-like break rules of `phtml.py` (a cut only after a relation, a binary operator or a comma at top level; never inside a bracket group of at most 12 characters).
- **Rows 1, 12, 24, 26 (blanks on p7, p20, p41; widows):**
  - rule (38) and the merged column of §12.1 (`part10`; rule (33)) remove the blank of p41;
  - p7 is now 84 % full (in version 3 a quarter of it was blank); §1.7 still starts on p8, because its heading, introduction, table header and two rows do not fit in the 16 % left;
  - rules (40)–(42) remove the widow and the orphan that the final `widows.py` found.
- **Rows 25, 27 (the §12.1 table):** `part9`, `part10`; rule (33).
- **Row 28 (references as bullets):** rule (34).
- **Row 3 and the loosest lines** (`gaps_text_words.py`, mean gap above 7 pt): `part5`–`part8`, wording only.

## 3. The math renderer: what was tried

1. **KaTeX 0.16.47** (copied with its manifest into `paper/katex/`). It was not used: rendering would have needed a JavaScript engine run under the watchdog for 1 400 formulas.
2. **MathML Core** (`pmath.py`). It was dropped because Chrome needs about 13 KB of memory per MathML element to print. Version 4 has 48 230 elements, and a test with 5 000 small formulas already reached 1.1 GB; the cap of 1.2 GB is not raised.
3. **HTML with STIX Two Math** (`phtml.py`). This was adopted. A build peaks at about 1.0 GB and takes 6 s.

The fonts are embedded as Type 3, as in version 3 (124 Type 3 fonts there): Chrome embeds the STIX Two variable fonts that way. A journal will typeset the paper again in its own system.

## 4. Found by the author's page look (after the checks)

1. **[GMMY24]: the scripts of `F_2^r` printed over the word before it.** The hanging indent of the references was inherited by the stacked script. Fixed in `phtml.py` with rule (39), `text-indent: 0` on stacked scripts and display limits.
2. **A widow on p14** (the last line of the proof of Corollary 3.4) and an orphan on p34. Chrome ignored `widows: 2` for a three-line proof. Rule (41) keeps every proof of fewer than 420 characters on one page (42 of 68 proofs).
3. **Two consecutive displays split across p32/p33.** Fixed with rule (42).
4. **Appendix A said that no table was broken across a page.** The tables of §12 run over several pages, row by row, with their header repeated. `part13` makes the sentence exact.

## 5. Two omissions of the record of version 3

`CORRECTIONS_v2_to_v3.md` does not list two edits that version 3 made. Both are listed in §13 of version 4:

- the rewording of Lemma 3.5;
- the explicit quantifier of Lemma 10.10, «for every `L ≥ 0` and every floor `f`».

## 6. Measures, version 3 against version 4

| check | version 3 | version 4 (build 27) |
|---|---|---|
| pages | 47 | 49 |
| statements split across pages (`structure.py`) | 5 | 0 |
| elements past the text block (`overflow.sh`) | not measured | 0 |
| largest right edge of a word (pt; text block 541.9) | — | 541.93 |
| lines with a gap above 6 pt / above 7 pt (`gaps_text_words.py`) | 13 / 1 | 10 / 0 |
| lines with a mean gap above 7 pt (`loose2.py`) | 1 | 0 |
| widows and orphans (`widows.py`, apart from the chapter start on p2) | 1 (p21) | 0 |
| pages under 90 % full, apart from the title page | p7, p20, p41 | p7 (84 %), p42 (75 %, the end of §11 before §12) |
| numbers of the tables of §1 and §12 (`md_vs_pdf.py`, as multisets) | OK | OK |
| references: cited, listed, alphabetical (`xrefs.py`) | 32 / 32 / yes | 32 / 32 / yes |

The 5 statements that `md_vs_pdf.py` does not match in order (Lemma 2.1, Corollary 2.3, Lemma 3.3, Lemma 9.7, Lemma 10.11) were read on the page (pp. 10, 11, 13, 30, 36). They are printed right; `pdftotext` reads stacked scripts out of order.

## Erratum (added on 5 October 2026, after cold reading 6; the lines above are left as they were written)

Cold reading 6 found four errors in this record. Our grading confirmed all four (`reports/LECTOR_FRIO_6/CALIFICACION_LECTOR_FRIO_6_v1.md`, item 4):

1. **Line 26 cites «items 7, 8 and 11».** There is no item 11 in this file. The ranges of §12 that the fifth reader checked against the code are items 7 and 8.
2. **The parenthesis on the 7 634 cells** that version 4 put in the row of the fourth reader in §12.2 was wrong. It said «7 874 less the 240 with `i = 0`». The author composed it and the fifth reader did not check it. The 7 634 cells are:
   - the 7 620 with `i ≥ 1`;
   - the 14 with `i = 0` and `I = ∅`, where `M = 0`.

   Version 5 corrects it.
3. **§5 says the rewording of Lemma 3.5 is listed in §13 of version 4.** It is not, and rightly: it was a change in a proof, not in a statement.
4. **§6 heads a row «pages under 90 % full».** `checks_v4/fill.py` marks pages under 85 %, so p. 23 (89 %) was left out of that row. `paper/checks_v5/fill.py` keeps the 85 % mark but prints every page, and §5 of `CORRECTIONS_v4_to_v5.md` lists the pages under 90 %.

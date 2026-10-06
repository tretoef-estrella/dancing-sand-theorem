# Corrections from version 2 to version 3 of «The Dancing Sand Theorem»

Grepy Bross, 5 October 2026.

## Files

| file | md5 |
|---|---|
| `paper/THE_DANCING_SAND_THEOREM_v3.md` | `e7365580b4470d234bc5bf17b076cc65` |
| `paper/THE_DANCING_SAND_THEOREM_v3.pdf` (47 pages, build 17) | `b1c910de09c3eed72f83298c939425c9` |
| `paper/THE_DANCING_SAND_THEOREM_v3.html` | `37b9e04d3d286bc63fd08dd5e9b7eb16` |
| `paper/md2html.py` (builder of version 3) | `7376bec1530bf9dcf58d9405faaf10b8` |
| `paper/build_v3.sh` | `51b4b3a5e5569e507cba1ca83292bc0d` |

- Version 2 (md, html, pdf) and `build_v2.sh` are now in `paper/historico/`.
- The builder of version 2 is `paper/historico/md2html_v2.py`. The builder at build 13 is `paper/historico/md2html_v3_build13.py`.
- Every edit is a script in `paper/v3_edits/` (`part1.py` … `part11.py`, 68 replacements). `lib.py` checks that each replacement matches its text exactly once.

**No statement of a theorem changed. Lemma 7.9 was strengthened**, from «integer separation» to «integrality».

## 1. Source: the grading of cold reader 4

The grading is `reports/LECTOR_FRIO_4/CALIFICACION_LECTOR_FRIO_4_v1.md` §4. Each item below names its script.

1. **«Even» payment systems** (`part1`). Remark (1) and Remark (2) of §10.5, and the statement and proof of Lemma 10.6(a).
   - The reader found the missing word in Remark (2). I found the same gap in Lemma 10.6(a), whose proof divides `S` by `2`.
2. **Lemma 7.9 is now «integrality», with its proof** (`part1`).
   - The proof is by induction on `|I|`, using the real part of Lemma 7.2(b) at non-strict cuts, then Lemma 7.3, the penalty shifts and the deletion at a cut.
   - A paragraph says where strictness is still needed: only in Proposition 9.6 (H).
   - §8 and Proposition 9.6 (H), (K) now cite the integrality.
3. **§1.2:** the rounding never acts in the cube (`part1`). The vocabulary row «raw clocks; pooling» says the same.
   - **Departure from grading item 3:** the general argument of the proof of Corollary 1.7 was kept unchanged. It is valid for every sequence, so nothing needed simplifying.
4. **§7.1** (`part1`):
   - a position where the fit drops strictly is a cut, since Lemma 7.1 is a condition on each level set;
   - the proof of Lemma 7.2(b) now says «(a strict drop of the fit is a cut)».
5. **Theorem 7.8, step 3** (`part1`):
   - case (c) now reads «`T = 0`, `sat = 1`, `J' ≢ 0`»;
   - case (d) lists the remaining cases and cites Lemma 7.7.
6. **Proposition 9.6 (H)** (`part1`): «`Z_1 ≤ 0`»; the largest big clock is the integral mean `μ`.
7. The junction value of the old proof is gone, because the new proof does not use it (`part1`).
8. **§1.0, §13, Appendix A** (`part2`):
   - the exact reading record: the repair of version 2 was read cold on 5 October (it holds);
   - the changes of version 3 are not yet read cold;
   - the «four entries» of Appendix A are named.
9. **§1.7, four wordings** (`part1`): the covariant system; the fit; «pays an even amount, `2^α(i + d)`»; «the tensor product of `V` with a Frobenius twist».
10. **§1.8 [Aky26]** (`part1`): the question quoted whole; «their reflections of odd grids».
11. **§12.1** (`part2`), with the gates re-run (§3 below):
    - the strict-cut row: 192 024 non-zero shifts, house-level controls 1 911/7 038 and 18 606/192 024;
    - a new row for Lemma 7.9, with its control (1 942 houses);
    - Theorem 7.8: «`I ≠ ∅` and `k ≤ 6`»;
    - Theorem 7.10: 1 638 cells on the whole printed range, with the raw-clock control (322 of 322).
12. **§12.2** (`part2`, `part3`, `part9`):
    - «Four readers»;
    - four rows for reader 4;
    - the old Lemma 7.9 named «the integer separation of adjacent level sets (Lemma 7.9 of version 2)» in the rows of readers 3 and 4.
13. **The pdf** (§2 below):
    - each case of Theorem 7.8 step 3, Theorem 7.10 and Proposition 9.3 is in its own paragraph;
    - formulas no longer break inside a sub-expression;
    - every page was looked at.

## 2. Source: the page look and the word-gap measure (presentation only)

### Builder rules added to `md2html.py`
- **(11)** each case of a proof starts a new line;
- **(12)** no line break:
  - inside a bracket group of at most 40 characters;
  - next to a fraction slash;
  - after a big operator with its scripts;
  - inside a page range;
- **(14)** no break before a binary operator or a relation;
- **(15)** «-th» is joined to its formula;
- **(16)** inside a formula, a line breaks only after an operator or a relation, or at a comma between formulas, as in TeX;
- **(17)** a formula of at most 40 characters never breaks inside a table;
- **(18)** a word joiner closes every braced exponent or index;
- **(19)** commas inside brackets never end a line;
- **(21)** an indented formula line is set as a display, also inside lists and boxes;
- **(22)** boxes never split across pages, and a table keeps its first three rows together;
- **(23)** no break between «)» and «(»;
- **(24)** no break after a relation when at most 3 characters of the formula follow («`= 0`» was alone on a line);
- **(25)** a file name without «/» never breaks and is never hyphenated (it had printed «`gate_-dance.py`»);
- **(26)** references at 9.6 pt, ragged right.

**Tried and dropped, both by measure:**
- **(13)** fixed-width spaces inside formulas: they pushed the stretch onto the words; lines with text gaps above 7 pt went from 2 to 24.
- **(20)** `text-wrap: pretty`: lines above 6 pt went from 13 to 28.

### Text changes, presentation only
- `part4`: the vocabulary table header reads «where».
- `part5`–`part8`, `part9`, `part10`: long formulas set as displays. Places:
  - Lemma 10.1, Corollary 6.3, Lemma 10.10, Corollary 10.2, Corollary 10.9, Corollaries 1.5, 10.17 and Theorem 10.22;
  - Proposition 3.1(b), Lemmas 3.2–3.3, §3.3, Theorem 3.8;
  - Propositions 5.2, 5.3, 9.3, Lemma 9.5, Corollary 1.7, Theorem 7.8 step 5, §8, the definition of `next(t)`;
  - Proposition 5.3 step 1 (on two lines), `glue(X, Y)`, Abel's sum in Lemma 7.1, `π'(f)` in Lemma 10.4.
  - The «In particular» of Corollary 1.6 became a list.
- `part11`: one loose line on p. 30 was reworded with the same content; «Corollaries 1.5, 1.6 (from the rule) and 1.7».
- **Found during this work:** about 25 bold formula lines meant as displays had been printed inline since version 1. Rule (21) sets them as displays.

### Result
| | version 2 | version 3 |
|---|---|---|
| justified lines with mean text-word gap above 7 pt | 10 | 1 |
| above 8 pt | 5 | 0 |
| words beyond the right margin | 0 | 0 |
| pages | 43 | 47 |

The pages went from 43 to 47 because of the displays and the new Lemma 7.9.

**Accepted:**
- **p. 7 ends about a quarter blank.** The introduction of §1.7, its table header and the table's first three rows are kept together.
- **p. 41 ends about a sixth blank.** A row of a table is never split.

## 3. Gates of version 3 (every log ends `VIGIA-FIN-OK`)

- **`gate/gate_strict_cut.py`** (md5 `150c315bfd45c8060170bc407c78feed`; version 2 in `gate_v2_record/`), log `logs/v3_gate_strict_cut_6_4.log`:
  - 16 380 houses, 8 001 boundaries, 0 strictness failures;
  - 192 024 non-zero shifts, 0 failures;
  - 360 deletions, 0 failures;
  - 0 non-integral fits;
  - controls fire: 1 911/7 038, 18 606/192 024, 1 942.
- **`gate/gate_sections5to7.py`** (md5 `3af09e09418ef0701d34b47ecf720bc5`), log `logs/v3_gate_57_127_3.log`:
  - Theorem 7.10: 1 638 cells, 0 bad;
  - the raw clocks are rejected in 322 of 322 cells;
  - Theorem 7.8 controls: 164 and 24 houses.
- **The reader's own scripts**, re-run from `reports/LECTOR_FRIO_4/delivered_2026-10-05/engines/` (`logs/LF4_rerun_*.log`): output identical to the reader's logs.

## 4. Builds

Builds 1–17: logs `logs/v3_build_*.log`; trial builds in `logs/v3_try_*.log`.

- **Build 16** was killed by the watchdog on memory (1.46 GB) after its pdf was written, so it does not count. Build 16b, the same command, ended `VIGIA-FIN-OK`. The caps were not raised.
- **Final: build 17**, 47 pages. Every page was looked at, in order: pp. 1–21 on build 13; pp. 22–48 on build 15; on builds 16b and 17, every page that changed.

— Grepy Bross

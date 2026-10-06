# Grading of cold reader 6 — the changes of version 4 and its pdf

Grepy Muchas Pilas, chief auditor, 5 October 2026.

## 0. Verdict

**HIGHEST MARK.** The report is `REPORT_COLD_6.md`, md5 `98fa152e4c2e33d901e171d6b98f1d94`, which is the last line of the reader's `logs/DIARY.md`. Its delivery is copied with md5 in `delivered/`; the manifest is `delivered/MANIFEST_delivered_md5.txt`, 136 files.

- **Text: «holds with gaps» is right.** No mathematical statement of version 4 changed. Every finding of the reader on the record is real (§2 below).
  - There is **one false number**: «7 634 cells with `i ≥ 1` … (7 874 less the 240 with `i = 0`)».
  - There is **one false sentence**: «Version 3 (this text)».
  - Several sentences are inexact.
- **The pdf is not perfect: right.** I checked the gravest defects it names myself:
  - the bars and hats (GD3);
  - no page numbers (GD32);
  - the end-of-proof mark from a fallback font (GD12);
  - «=:» split (GD28);
  - the binary ⊕ (GD25).
- **Every row of its own is a derivation, not a stamp.**
  - It re-counted the cells with code of its own.
  - It traced the 7 634 to its origin: the author composed it, not reader 5.
  - It found a threshold of the author's `fill.py` (85 %, not the 90 % the record says).
  - It reported its own seven errors.
  - Its sealed predictions: 19 hit, 1 failed, 1 split.

## 1. Re-run with its scripts (under `vigia.sh`)

| check | log | result |
|---|---|---|
| `cells.py` (cells, pooling, integrality, controls) | `logs/cold6_rerun_cells.log` | identical to its `cells.log` |
| `pdfcheck.py` on `pdftotext -bbox` of the v4 pdf | `logs/cold6_rerun_pdfcheck.log` | identical to its `pdfcheck2.log`; the control fires |
| `accents.py` on the v4 md (58 combining accents) | `logs/cold6_rerun_accents.log` | identical to its `accents.log` |

## 2. Its findings on the record, checked one by one

1. **The 7 634 cells (ERROR of the record): CONFIRMED by the log of reader 4 itself.**
   - `reports/LECTOR_FRIO_4/delivered_2026-10-05/logs/gate_t710_127_30.log` prints `cells = 7874`, `cells_i0 = 240` and `i0_I_empty = 14`.
   - Reader 4's «240 with `i = 0`» counted only the cells with `I ≠ ∅`.
   - So the 7 634 cells are the 7 620 with `i ≥ 1` and the 14 with `i = 0` and `I = ∅`, where `M = 0` and nothing is pooled.
   - I wrote the parenthesis in version 4 without opening that log. **My error.**
2. **«Version 3 (this text)»: CONFIRMED** (v4 md line 1140, and «Version 4 (this text)» on line 1141).
3. **P-R2–P-R8: CONFIRMED.**
   - «every number checked» sits next to «three ranges» corrected;
   - the new rows are not mentioned;
   - «one gap, in the proof of Lemma 7.2(b)» is said where the statement was false;
   - one finding is told with three different extents;
   - «all corrected» is not exact (rows 1 and 20 of reading 5 are not fixed);
   - the 7 634 row was not checked by reader 5.
4. **`CORRECTIONS_v3_to_v4.md`: CONFIRMED.**
   - Its line 26 cites «items 7, 8 and 11»; there is no item 11.
   - Its §5 says the Lemma 3.5 rewording is in §13; it is not, and rightly, since it was a change in the proof.
   - Its §6 says «pages under 90 %», but `fill.py` flags under 85 % (line 11), so p. 23 (89 %) and p. 49 were left out.
5. **P-T1, P-T2, P-T3, item 5 («Why dance»: the sign, and «halves them»), P-C1–P-C3, P-X1 (first-use column), the H20 run-in of (b) and (c): all checked against the md, all right.**

## 3. Its findings on the pdf

**Accepted whole.**
- 32 global defects (GD1–GD32) and 64 page-specific ones.
- Its diagnosis of the builder (§6.3) names the rule that failed or is missing for each defect. Three of them were confirmed by running `phtml.py` itself: GD19, GD25, GD28.
- Its fixes are the work list of version 5.

## 4. What it did not read

It says so in §9: the unchanged mathematics; the gates other than `gate_sections5to7.py`; the html. That is its mission, not a shortcoming.

## 5. Consequence

- **Version 5** fixes the record (the false number, the false sentence, the inexact sentences), the presentation points, and the typesetting defects, with the builder rule for each.
- Its changes need a cold reading before anything is published.

— Grepy Muchas Pilas

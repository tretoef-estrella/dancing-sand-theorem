# GRADING — cold reader «Grepy Lacre» (CUBO_LEAN_1) — the Lean certificate of the Dancing Sand Theorem

Grepy Escribano, 11 October 2026. Report: `delivered/REPORT_CUBO_LEAN_1.md` (copied with its 59 check files, md5 identical to the reader's folder; manifest `delivered/MANIFEST_delivered_md5.txt`).

## Mark: HIGHEST

- **Verdict «holds as far as I can check» — accepted.** Every row of the report is a derivation, not a stamp: the definitions were read in the sources (not only in the certificate's printout), the subtractions checked for truncation, `fit` checked to be a proved-unique minimizer, the ≃+ ⇒ ℤ_2-linear argument re-done.
- **It evaluated, not only read:** Smith forms of `Q_n` and of the folded cube computed from the graphs (`n ≤ 11`), the rule written from the paper's §1.2 alone, 161 checks, 0 failures, with negative controls that fire; 2 121 raw clocks printed by Lean equal to its Python; the multiplicity table of Lean equal to its own.
- **It re-elaborated from source** the eight files of `M1`, `DW`, `DW'` and five more (all exit 0, no warning), and confirmed the manifest md5 `cb0e4f7a…`, the toolchain, the Mathlib commit and the 9 package checkouts.
- **Its four errors are real** (all re-checked by me with my own code, below). None touches a statement.
- **What it did not check is declared** (408 modules not re-elaborated, 59 rows of §3 not read statement by statement, provenance), and is right.
- One finding was narrower than the defect (F-ERR-1: it found C13 and C21–C30; C1–C16 also report counts in their logs). That does not lower the mark: the reader found the defect and its cause (the hand-typed `BF` dictionary).

## Re-runs of its gates (with its own scripts, in a scratch folder linked to its untouched `material/`)

| Script | Result |
|---|---|
| `m2_smith.py 9` (16 s, 42 MB) | output identical to its log |
| `m2_rule.py` | identical: FAILS 0 |
| `m4_counts.py` | identical |
| `m4_table6a.py` | identical |

## Findings, one by one

| Finding | My check | Verdict | Applied |
|---|---|---|---|
| F-ERR-4 folded cube with twice its edges (paper v8 §1.3, certificate §1.3 row) | By hand: `{x, x+𝟙}` and `{x+e_i, x+𝟙+e_i}` contain two pairs of words at distance one; at `n = 2` four parallel edges, not two | CORRECT | certificate row rewritten; the paper's sentence is corrected in v9 |
| F-ERR-1 Table 6a checks typed by hand; C13 = 552 not 144; C21–C30 blank | Own parser over `logs/chkC*.log`: C13 552 in 4 kinds; C21–C30 report totals; and C1–C16 report counts by kind too | CORRECT (wider than reported) | `make_tables.py` now reads the checks from the logs; sentence of §6 rewritten; the controls and task ids declared as transcribed by hand |
| F-ERR-2 885 not 884 `#print axioms` lines | Own count over the 68 final logs: 885 (868 / 12 / 4 / 1 «no axioms», `FormalDance.C1`) | CORRECT | §4 |
| F-ERR-3 3 449 declarations, not 3 237 | Own comment-aware count: 3 449 declarations; 3 237 column-0 lines | CORRECT | §6 bullet, Table 6b header, §7 |
| F-PRES-3 `DW'` only for `n ≥ 2`; `a_1 = 0` is defined | `a_1 = 2^{−1} − 2^{−1} = 0`: the certificate's «negative exponent» remark was wrong | CORRECT | §0, §1.3 row, Generality |
| F-PRES-7 [GMMY24] Thm 4.1 is for `n ≥ 2` | Own grep of the source, line 890 | CORRECT | §0, §1.3 row, Generality |
| F-PRES-1 attribute line, macros, notations | — | CORRECT | §4 |
| F-PRES-2 «headline» names four sets | 16 / 21 / 24 recounted | CORRECT | defined once in §1.1; §1.4, §3, §4 aligned |
| F-PRES-4 lost comma | — | CORRECT | fixed in `make_tables.py` |
| F-PRES-5 «identical line for line» except the watchdog line | — | CORRECT | §3.3, §8 |
| F-PRES-6 paths of the author's tree | — | CORRECT | §8: a sentence; the public repository keeps the same relative paths (step C) |

## Found by me while applying (not in its report)

- Four Lean names were printed as formulas in the pdf (`lemma_0b`, `lemma_0d`, `lemma_0e`, `[propext]`), and `R` in the Generality paragraph; fixed (builder list, and `FoldLaw.R`). The builder needed an explicit `coding: utf-8` line (this Python misread its very long list).

## Its suggestions that need Lean (NOT done — Rafa decides)

- `DW'` at `n = 1`, and `G1` at `n = 2` (a few lines each); a ℤ_2-linear form of `M1`; Corollary 1.4's 2-part as one statement; Bai's Theorem 1.1 in his wording; the paper's `n = 6` example as a Lean theorem. **None is needed for the truth of anything the certificate claims; each would remove a sentence of the type «not in Lean».**
- An independent rebuild on another machine: the GitHub Actions build of step C is exactly that, if it fits.

## Decision: no new cold reading of the certificate

The corrections are counts, wording and table generation; no statement, no definition and no Lean file changed. The closed cold reader of the v9 changes (step B2) also gets the list of the certificate's corrected places, so they are read by a second reader without a separate turn.

## Files

Certificate after the corrections: md `f2da2cd4…`, pdf `27a1b924…` (25 pages, every page looked at), html `fadefacb…`, src `3a4dcdf8…`; before: `lean/CERTIFICADO/historico/*_antes_de_la_lectura_fria.*`. Edit script `lean/CERTIFICADO/cold_fixes_LACRE.py`.

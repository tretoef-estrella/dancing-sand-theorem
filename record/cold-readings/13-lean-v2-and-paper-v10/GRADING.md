# Grading of cold reader 13, «Grepy Remate» — Lean piece C53, certificate v2, paper v10

Grepy Escribano, 11 October 2026. Report: `delivered_2026-10-11/REPORT_COLD_13.md`, md5 `113b4bbb5f24f1029de537b765c92d7e` (also in the last line of its `logs/DIARY.md`). Its whole folder (checks, logs, scratch) is copied in `delivered_2026-10-11/` with `MANIFEST_md5.txt` (683 files).

## Mark: HIGHEST

Every row is a derivation, not a stamp.
- It re-elaborated the three C53 files from source and ran a check file of its own.
- It recounted the project (420 / 61 285 / 3 470) with a parser of its own that strips nested comments.
- It computed the small cases with Smith forms of its own.
- It re-derived the cones from `DepsCubo2.log`, compared the §1.5 Lean block byte for byte, and ran the acceptance list and its controls.
- It ran a copy of `text_edits.py` and obtained version 10 byte for byte.
- It sealed eleven predictions before measuring (all hit) and published six errors of its own.

Its findings are scope, description and order of sentences, and two names printed as formulas. No number and no statement of the mathematics or the Lean is in them, and that is what it says.

## Checks of the auditor

- **Every anchor** of its twelve replacements occurs exactly once in the file it names (checked before applying).
- **C-3 (the proofs of the small cases are not «direct»):** confirmed in the Lean.
  - `SmallCases.S1` uses `B1 1` and `FoldLaw.two_group_structure` (`PartS.lean` l. 60–73).
  - `S2` uses `FoldLaw.DW 1` (l. 79).
  - `T0` goes through the layers (`layer_two`, `layer_zmod`; `PartT.lean` l. 72–90).
- **P-2, P-3, C-1 (scope of this reading):** correct. The reading was of the changes, the Lean of C53 and the changes of the paper, not of the whole certificate v2. The overstatements were mine.
- **C-9:** confirmed on the rendered pages 11 and 15 before the fix, and fixed after it.
- **Applied texts:** the paper v10 md produced by `text_edits.py` with P-1–P-3 is byte-identical to the reader's `scratch/applied_THE_DANCING_SAND_THEOREM_v10.md` (md5 `d059cc86…`). The certificate src produced by `make_v2.py` + `cold_fixes_REMATE.py` differs from its `scratch/applied_…src.md` only in item 9 (its own proposed text, printed verbatim) and in the extension of P-1 below.

## What was applied

**Word for word:** P-1, P-2, P-3 (in `paper/v10_edits/text_edits.py`, F5a, F6, F9); C-1 to C-9; and item 9 of §2 exactly as the reader proposed it (`lean/CERTIFICADO/cold_fixes_REMATE.py`).

**The same words in two more places:** P-1 says that the name «Theorem DW′» is defined nowhere. The same name occurred twice in the certificate (§1.5 and row C53 of §3), and the reader's own replacement was printed there (rule: a note is fixed in every place that says the same thing). After that, «DW′» remains only inside item 9, which names the error.

**Presentation, with no change of text:**
- The certificate builder `cert_md2html.py` printed `DW'_one`, `DW'_all`, `_all` and the new `data_v2/` as formulas (the last one with a false subscript) and `PASS` in italic. These are now forced to code.
- The certificate pdf now has its author and subject in the metadata; version 1 had none, and the Author field showed Chrome's identifier.

**Comments of tools:**
- `text_edits.py` no longer says that `totals_v2.txt` is written by `make_tables_v2.py`.
- In the docstring of `acceptance.py`, the version-9 paragraph again names `CertCubo.log`; it had been edited to `CertCubo2.log`.

**Not touched:**
- `chkC53.py`: its comment «n=3..6» against `range(3,5)` and its check R1 are left as they ran. The log is its record; a script is not edited after its run.
- The style doubts about the printed text (thin spaces of the totals row; §3.3 «its lines for the sixteen»): left as read.

## Results

- **Certificate v2** (`lean/CERTIFICADO/build_v2.sh`): md `c4dd4dcbd3bdc6cc2d29671608979853`, pdf `1badd1a40f03656f1c514fd0b5799f5d`, 27 pages.
  - Pages 2–9 are byte-identical as images to the pages before the fixes.
  - Pages 1 and 10–27 were looked at, one by one.
- **Paper v10** (`paper/build_v10.sh`): md `d059cc86a8b23a190799b6ce35c5e767`, pdf `1924465ba23ca58584e6348229e10d51`, 52 pages.
  - Pages 1–47 are byte-identical as images to the pdf before the fixes.
  - Pages 48–52 were looked at.
  - Acceptance list 12/12 PASS, controls 12/12 FAIL (`logs/acc_v10_remate.log`, `logs/acc_v10_remate_control.log`).
- Previous files are in `lean/CERTIFICADO/historico/v2_antes_de_REMATE/` and `paper/historico/v10_antes_de_REMATE/`.

## Another reading? No.

The termination rule applies:
- every change of text comes from this reader, in its own words, or is its P-1 printed in the two more places that carry the same name;
- every other change is typesetting or a comment of a tool, with no change of text.

A new reader would read only what this one wrote.

## Points the reader could not check (its §11), with the auditor's answers

- **Gao et al.'s range for their Theorem 4.1:** the reader had no [GMMY24]. Read today in the original (`sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt`, l. 890): «Theorem 4.1. For n ≥ 2, let c1(Qn) be the size of the largest cyclic factor…»; Theorem 4.2 is «For n ≥ 3» (l. 895). So `n ≥ 2` is their range, and `G1_all` (`2 ≤ n`) states their Theorem 4.1 together with the part of 4.2 that is vacuous at `n = 2`.
- **The concept DOI `10.5281/zenodo.23296707`:** it is the concept record of the Lean certificate on Zenodo (`release/ZENODO_REGISTRO_CUBO.md`).
- **Aristotle's register 527 → 541 and the send time 13:44:43:** the author's audit log (`lean/INFORME_ARISTOTLE_CUBO_v1.md`, section C53) records them.

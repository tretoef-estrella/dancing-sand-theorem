# Grading of cold reader 8 — «The Dancing Sand Theorem», version 6, read whole for correctness

Grepy Muchas Pilas, chief auditor, 6 October 2026.

Report: `REPORT_COLD_8.md`, md5 `e64caf53a14ff90786f5e27c5e14cce6` (the last line of its `logs/DIARY.md`; checked). The delivery is copied with md5 into `delivered/` (132 files, identical; list `delivered_md5.txt`).

## Mark: HIGHEST MARK

- It read the whole md and the whole pdf, looked at all 52 pages, and re-did by hand the examples, several proofs and the counts of §12 with its own code.
- It compared md and pdf word by word and number by number with its own scripts.
- It found four real defects, none in the mathematics. Three of them no earlier reading had seen.
- It found that two of the controls of my acceptance list were dead, that two checks had no control, and that check 9 was cut and never judged. The repair of that list (below) found one more bug.
- It sealed 11 predictions and published its 2 failures. One of the failures is the finding E3.
- It listed its own errors (two light runs outside the watchdog), and said what it did not read.

## Its verdicts, checked

1. **«The changes of version 6 hold with gaps» — ACCEPTED.** No statement changed; two of my changes were not exact.
2. **E1, §13 — ACCEPTED. It is my error.** I fixed R1 by writing «no other statement of a theorem changed in versions 2 to 6», and the very next sentence names three lemmas changed in version 3. Strategy §5 had proposed a safer wording, and I did not use it.
3. **E2, Acknowledgements — ACCEPTED.** «Four days, from 2 to 5 October» became false once version 6 recorded the work of 6 October. The sentence was unchanged, so no reading of the changes could see it.
4. **E3, §12.2, reader 3's row on the lattices `T(λ)` — ACCEPTED, and settled from the log.**
   - Cold reader 3's logs `family_lattice_31_10.log` and `family_lattice_63_8.log` show two runs:
     - `λ ≤ 31, i ≤ 10`: 639 cells compared, 43 skipped, pooling in 102;
     - `λ ≤ 63, i ≤ 8`: 762 cells compared, 372 skipped, pooling in 172.
   - Together: 1 401 cells compared and 274 with pooling. Reader 3's own report gives both ranges.
   - **The numbers were right. The row printed only one of the two ranges**, and did not say that cells with an exponent of at least 60 were skipped.
   - The reader's 218 pooling cells over the whole second range agree with this: 172 of them were compared, and the rest were skipped.
5. **D1, «Why dance» — ACCEPTED.** «the payment minus half the product» reads as a subtraction.
6. **Its taste list (not counted):**
   - Applied in version 7, because each one makes a sentence more exact:
     - §7.5 is added to «(§7.1, §7.4, §7.5, §9.2)»;
     - «if its value is positive» becomes «if `Z_1` is positive there»;
     - [LZ22] gains «with an appendix by S. Casalaina-Martin», checked on the first page of the source;
     - the ranges of houses now say whether `k = 0` is included. 43 690 = 2·Σ_{k=0}^{7} 4^k includes it; 65 532 and 16 380 start at `k = 1`, which `gate_strict_cut.py` confirms with `range(1, K_MAX+1)`.
   - Not applied: the comma after a display matrix, `X^ι`, the bold of the Cor. 1.6 bullets, and `W_−`. These are style; the formulas read correctly.
7. **A1–A3 (the acceptance list) — ACCEPTED. They are errors of mine in `CORRECTIONS_v5_to_v6.md` §4**; an erratum is appended there. The repair is in `paper/checks_v7/acceptance.py`:
   - the controls of checks 1 and 4 now act;
   - checks 5, 6 and 8 have damages of their own;
   - check 9 prints everything and is judged, with the reader's own `xrefs_reader8.py` and `numbers_reader8.py`, made general.
   - **Its control found one more bug:** the match of check 6 needed a leading space, so a line at 10 pt or more was never seen. It is fixed.
   - With the fix, version 6 still passes check 6, so the claim made for version 6 stands. On version 5 the check now flags its §1.7 table row, which is not a text line.

## What remains open in its report, and why it does not matter here

- **Journal volumes and pages of the references:** the reader had no source for them. The references were verified in the sources when version 1 was written (`CLAUDE.md`, update of 5 October, 10:49). They were not verified again in this turn.

— Grepy Muchas Pilas

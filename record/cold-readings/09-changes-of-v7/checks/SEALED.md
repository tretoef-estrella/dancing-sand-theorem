# Sealed predictions — cold reading 9
Sealed before measuring. Each is graded in REPORT_COLD_9.md §8.

Sealed at: see logs/DIARY.md line «SEALED P1–P7».

- **P1.** `diff -u v6.md v7.md`, run by me, gives the same 10 hunks as DIFF_v6_to_v7.txt (only the timestamp lines may differ).
- **P2.** Arithmetic, with 4^k houses per (k, α), α ≥ 1: Σ_{k=0..7} 4^k = 21 845, ×2 = 43 690 (k = 0 included, α = 1, 2); Σ_{k=1..7} 4^k = 21 844, ×3 = 65 532 (k = 0 excluded); Σ_{k=1..6} 4^k = 5 460, ×3 = 16 380 (k = 0 excluded). All three ranges as printed in v7 will hold.
- **P3.** The two logs of reader 3 give: run (λ ≤ 31, i ≤ 10) 639 compared, 43 skipped, 102 where pooling acts; run (λ ≤ 63, i ≤ 8) 762, 372, 172; and the cell totals are 682 = 31·11·2 and 1 134 = 63·9·2 (λ from 1, i from 0). 639 + 762 = 1 401 and 102 + 172 = 274 (the old row's numbers were the sums). The row will hold.
- **P4.** gate_strict_cut.py loops over k from 1 (not 0) up to 6, and α = 1, 2, 3.
- **P5.** Rendering both pdfs and comparing gives exactly the changed pages 1, 2, 3, 9, 30, 44, 46–52 (14 pages); v6 and v7 both 52 pages.
- **P6.** acceptance.py on v7: 9 of 9 pass; control mode: 9 of 9 fire; both logs end in VIGIA-FIN-OK.
- **P7.** The §13 sentence on versions 2 to 7 will be consistent with Appendix A of v7 as far as the text shows; I expect at most a PRESENTATION point (e.g. whether Remark (2) of §10.5 or §12 rows count as «numbered statements»), no ERROR.

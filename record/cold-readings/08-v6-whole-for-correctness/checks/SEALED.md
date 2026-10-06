# Sealed predictions — cold reader 8
Each line written BEFORE the measurement; result added after, in the same size of type.

S1 (2026-10-06, before scratch/py/counts.py): enumeration with λ ≥ 1, i from 0, houses with k ≥ 1 reproduces every count of §12 that is a pure count of cells/houses/clocks/entries: 7 874 = 254 + 7 620, 240 with i = 0 and I ≠ ∅, 14 with i = 0 and I = ∅, 7 634; 10 455, 10 200, 9 880; 16 380, 16 002, 65 532, 48 006; 14 560, 301, 109 200; 1 638. Odds: 95 % all hold.
S1 RESULT: HIT. All 17 counts reproduced (`logs/counts.log`). The prediction could fail: it fixed the conventions (λ from 1, i from 0, k from 1) in advance; with λ from 0 the first count would be 7 936, with k from 0 the houses would be 16 383.

S2 (before logs/acc_v6.log): acceptance.py plain on v6 gives PASS on all nine checks, as CORRECTIONS §4 says. Odds 85 % (risk: another poppler version on this machine).
S3 (before logs/acc_v6_control.log): in `control` mode on v6, checks 1, 2, 3, 4, 7 FAIL, but checks 5, 6 and 8 PASS, because the control damages only `raw`, `md` and the in-memory `B`, while fill.py and loose.py re-read the undamaged bbox file from disk and no hyphen is damaged. So MISSION §3.3's «every check but 9 must FAIL» will NOT be met. Odds 85 %.
S4 (before logs/acc_v5.log): plain mode on v5 (v5 md, v5 pdf) fails exactly checks 1, 4 and 8, as the author's run; the others pass. Odds 60 % (check 6's NOT_TEXT exceptions are positions of v6, and v5 may have a text line at 3×).
S2 RESULT: HIT. All nine PASS on v6 (`logs/acc_v6.log`).
S3 RESULT: HALF FAILED. I was right that 5, 6 and 8 PASS in control mode, and that the mission's «every check but 9 must FAIL» is not met. I was WRONG about checks 1 and 4: they PASS too. Only 3 of 8 controls fire (2, 3, 7) (`logs/acc_v6_control.log`). Cause, found after the run (`logs/rawdiag.log`): `pdftotext -raw` gives «2.(Λ).» with no space, so `raw.replace('2. (Λ).', …)` changes nothing; and the fake widow is inserted at y = 100 pt while every page's real first line is at y ≈ 54–64 pt, so it never becomes the top line.
S4 RESULT: HIT. v5 fails exactly 1 («2. (Λ).», «3. (Cut).»), 4 (p. 20) and 8 («‑mod-/ules», «spa-/ces).», «‑lat-/tices,») (`logs/acc_v5.log`).

S5 (before scratch/py/pooling_counts.py): my own code, from the definitions of §1.2, §5, Prop. 5.4 and §7.3 only, reproduces
  (a) 322 cells where pooling changes the raw clocks, λ < 64, i ≤ 12, α = 1, 2 (§12.1) — odds 70 %;
  (b) 1 876 such cells for λ ≤ 127, i ≤ 30, α = 1, 2 (reader 3) — 70 %;
  (c) 1 834 of them with i ≥ 1 (reader 4) — 75 %;
  (d) 274 for λ ≤ 63, i ≤ 8, α = 1, 2 (reader 3) — 60 % (that row's 1 401 cells do not factor, so its range may not be what it prints);
  (e) 2 316 of 9 880 cells (λ ≤ 255, 1 ≤ i ≤ 40, I ≠ ∅, α = 1) where the raw clocks with 1 added at the first dancer have a non-integral block mean — 70 %;
  (f) 1 942 of 16 380 houses (k ≤ 6, α ≤ 3) where x_H with 1 added at its first dancer has a non-integral fit — 75 %;
  (g) and no non-integral fit of x_H in any house with k ≤ 7, α ≤ 3, nor of the clocks of any cell above (Lemma 7.9) — 97 %.
S5 RESULT: (a) HIT 322; (b) HIT 1 876; (c) HIT 1 834; (e) HIT 2 316 of 9 880; (f) HIT 1 942 of 16 380; (g) HIT 0 non-integral (65 532 houses, and every cell of (a)–(d)). (d) MISS: for λ ≤ 63, i ≤ 8, α = 1, 2 my code finds 218 cells where pooling acts (and the range has 1 134 cells), not 274 (and 1 401). Since six counts of the same code hit, I take (d) as a fact about the printed row, to be explained (`logs/pooling_counts.log`).

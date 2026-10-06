# SEALED predictions (sealed BEFORE measuring, with odds)

## Sealed 2026-10-05 16:36:16, before writing any code (Part 2, my own gates)

- **S1** (hand counterexample, new): `x = (1, 2, 0, 3)`, `δ = (1, 1, 0, 0)`. `x` is cut at 2, not strictly (`fit(x) = (3/2)^4`). Integer fit of `x + δ` = `(3, 2, 2, 1)`; integer fit of `x` plus `δ` = `(3, 3, 1, 1)`. The engine will confirm both. Odds 98 : 2 (only risk: a slip in my hand PAVA).
- **S2** a systematic search will find counterexamples of length 4 with δ a 0/1 step, and none of length ≤ 3 (my argument: a non-strict cut with a non-integer common value needs ≥ 2 positions on each side). Odds 90 : 10.
- **S3** restated Lemma 7.2(b) on random integer sequences (length ≤ 10, δ integer non-increasing, changing only at strict cuts): 0 failures, of the real part, of «same level sets», and of the integer shift. Odds 98 : 2.
- **S4** control of S3 (δ with a jump at a non-strict cut): the integer claim fails in a positive fraction, between 5 % and 60 % of the trials where such a cut exists. Odds 70 : 30 for the interval; 97 : 3 that it fails at least once.
- **S5** Theorem 7.8 strict (Cut) on all houses with `1 ≤ k ≤ 6`, `α ≤ 3`: 16 380 houses, 0 failures; the number of houses with `J_H ≢ 0` is exactly 8 001 (= 3·Σ_{k=1}^{6} 2^{k−1}(2^k − 1), counted by hand). Odds 97 : 3 for 0 failures; 99 : 1 for 8 001.
- **S6** the construction of `V` (steps 1–8) with `c_F` at either end of the interval: (E), (M), (G), (Λ) hold in every house of S5. Odds 95 : 5.
- **S7** controls of S5–S6: (i) `c_F` one above the top of the interval breaks (M) or (G) in some house; (ii) the penalty shift moved one position later than the strict cut breaks the integer-shift identity in some house. Odds 90 : 10 for (i), 80 : 20 for (ii).
- **S8** Lemma 7.9 (integer separation) holds in every house of S5, after every penalty shift with `P_r, P_c ≤ 4` (only one of them non-zero, as in a real cell, and also both non-zero), and after the deletion at `ℓ = 2^k − 1`. Odds 95 : 5.

## Outcomes of S1–S4 (measured 2026-10-05, logs/fitlib_selftest.log, logs/gate_l72_mine.log)

- **S1 HIT.** `(1, 2, 0, 3)`, `δ = (1, 1, 0, 0)`: integer fit of `x + δ` = `(3, 2, 2, 1)`, integer fit of `x` + `δ` = `(3, 3, 1, 1)`, as sealed.
- **S2 HIT.** No counterexample of length 2 or 3 (entries 0..6); 38 of length 4 (entries 0..5, jumps 1 or 2), 48 of length 5 (entries 0..3). Caveat I did not foresee: the lexicographically first one, `(0, 1, 0, 1)`, is the text's own example translated by `−3`; translation is not «new».
- **S3 HIT.** 50 000 random sequences: 0 failures of the real part, of «same level sets», of «strict cuts stay strict», of «cuts stay cuts», of the integer shift.
- **S4 HIT.** Control B1 (one jump at a non-strict cut): the integer claim fails in 736 of 9 939 trials = 7.4 % (inside the sealed 5–60 %). The real part never fails at a non-strict cut (0 / 9 939), as Lemma 7.2(b) says. Control B2 (jump at a non-cut) breaks the real part in 45 043 / 45 043.
## Outcomes of S5–S8 (measured 2026-10-05, logs/gate_houses_k3.log, logs/gate_houses_k6.log)

- **S5 HIT.** 16 380 houses (`1 ≤ k ≤ 6`, `α ≤ 3`), strict (Cut) at the first dancer with `J_H = 1` and at its mirror, checked by the definition of a cut: 0 failures. Houses with `J_H ≢ 0`: **8 001**, as computed by hand.
- **S6 HIT.** `V` built by steps 1–8 with `c_F` = lower end and = upper end of the interval: (E), (M), (G), (Λ) hold in all 16 380 houses; also every intermediate claim of step 7 (final segment, `c_3 = max`, `c_4 = min`, `v'(p^*) < v'(p)`, interval non-empty) and Lemma 7.7's formula for `d_1`.
- **S7 HIT.** (i) `c_F` = top + 1 breaks (M) or (G) in 2 358 houses (and bottom − 1 in 2 358); `c_F := v'(I')` in 140. (ii) The penalty shift moved one position later breaks the integer-shift identity in 17 354 of 168 912 trials.
- **S8 HIT.** Lemma 7.9 separation: 0 failures on the houses, on 192 024 non-trivial penalty shifts (`P_r, P_c ≤ 4`, all 24 non-zero pairs, on the 8 001 houses with `J_H ≢ 0`), and on the 360 deletions at `ℓ = 2^k − 1`.
- Not sealed, observed: 3 180 of the 16 380 houses have a non-strict cut somewhere (17 238 non-strict cut positions in all). So strictness at the `J`-boundary is not automatic: the strict-(Cut) check could have failed.
## Sealed 2026-10-05 16:50:28, before writing engines/gate_t710_mine.py

- **S9** Theorem 7.10 against the 2-adic Smith form of the matrix `M^{(α)}(λ, i)` of Theorem 4.4 (built from the closed form, Smith form by min-valuation elimination modulo `2^P`), `λ ≤ 63`, `0 ≤ i ≤ 12`, `α = 1, 2`: the Smith exponents equal `αK + κ(m, K) + ŷ_D` (`i ≥ 1`) and `∞, αK + ŷ^♯_D` (`i = 0`) in every cell. Odds 96 : 4 (the risk is mostly a bug of mine in building `M`).
- **S10** controls of S9: the raw clocks (no pooling) are rejected in every cell where pooling changes the sequence; the integer fit with the floors first (wrong rounding order) is rejected in some cell. Odds 95 : 5 and 85 : 15.
- **S11** among the cells of S9 with `i ≥ 1`, at least 10 % have a non-zero penalty shift **and** a level set of size `≥ 2` (cells where the repaired step is really exercised). Odds 75 : 25.
## Outcomes of S9–S11 (measured 2026-10-05, logs/gate_t710_63_12.log)

- **S9 HIT.** 1 638 cells (`1 ≤ λ ≤ 63`, `0 ≤ i ≤ 12`, `α = 1, 2`), Smith form of `M` = Theorem 7.10's prediction in all; the Main-Theorem route (raw clocks of §1.2, pooled) agrees in all 756 cells with `α = 1`, `i ≥ 1`.
- **S10 HALF HIT, HALF MY ERROR.** The raw clocks are rejected in 306 / 306 cells where pooling acts (hit). The floors-first control **never fired, and could not**: I compared *sorted* lists, and the floors-first and ceilings-first roundings of a level set give the same multiset. A check whose control cannot fail is not a check; I replace it (S12).
- **S11 MISS.** Cells with `i ≥ 1`, a non-zero penalty shift and a level set of size `≥ 2`: 125 of 1 524 = **8.2 %**, below the sealed 10 %.
## Sealed 2026-10-05 16:51:43, before the corrected gate_t710_mine.py

- **S12** replacement controls for Theorem 7.10: (i) the real fit rounded half up, position by position, is rejected in some cell; (ii) the penalty shift applied one position after its strict cut (on `x_H`, then integer fit) is rejected in some cell. Odds 80 : 20 and 85 : 15. And: some cell has a level set with non-integer mean (otherwise the integer part of Lemma 7.2(b) would be vacuous on real cells). Odds 85 : 15.
- **S13** the same gate on `λ ≤ 127`, `i ≤ 30`, `α = 1, 2`: 0 failures. Odds 95 : 5.
## Outcomes of S12–S13 so far, and a new seal (2026-10-05 16:58:30)

- **S13 HIT.** `λ ≤ 127`, `i ≤ 30`, `α = 1, 2`: 7 874 cells, 0 failures (logs/gate_t710_127_30.log). Late-penalty control rejected in 1 904 / 1 904; raw clocks rejected in 1 834 / 1 834 cells with `i ≥ 1` where pooling acts.
- **S12 (ii) HIT** (late penalty rejected 232/232 at λ ≤ 63, 1 904/1 904 at λ ≤ 127). **S12 (i) and S12 «some non-integer mean» MISS:** in all 7 634 cells with `i ≥ 1` no level set has a non-integer mean, so control (i) can never differ from the truth there — again a control that cannot fail on this range.
- **S14 (sealed now, before the scan)** over all houses `k ≤ 7`, `α ≤ 3`, every `ℓ`: some house has a level set with non-integer mean. Odds 70 : 30. If yes, the first ones have `α ≥ 2` or `ℓ ≥ 30` (outside the cells above). Odds 60 : 40.
- **S14 MISS.** logs/scan_nonintegral.log: **no** house with `k ≤ 7`, `α ≤ 3` (65 532 houses, every `ℓ`) has a level set with non-integer mean, and none of the `i = 0` deleted sequences. Afterwards (not sealed, so not counted as a hit) I found the reason, a two-line induction: `fit(x_H)` is integer-valued in every house (REPORT §2.5).
## Sealed 2026-10-05 17:11:06, after reading the author's gates, before running any of them

- **S15** `gate_strict_cut.py 6 4` prints houses 16 380, bnd 8 001, pen_checks 393 120 (= 24 × 16 380, i.e. it counts the zero shifts of the 8 379 houses with `J ≡ 0`), del_checks 360, every *_fail 0, and both control lines True. Odds 95 : 5.
- **S16** `gate_lemma72.py 9 20000`: (A) and (B) 0 failures; control «189 of 2 841», exactly as printed in §12.1 (same seed 2026). Odds 85 : 15 (the risk: a different Python random stream).
- **S17** `gate_theoremO.py 5`: 69 cases, 0 with count ≠ 1; controls 42 and 26. Odds 95 : 5.
- **S18** `gate_remark2.py`, seed 11: generic/rand 245 of 248 clean (3 unclean, all at `l = 63`); oddU/rand 169 of 248 clean (79 unclean, first at `l = 32`); generic/eta and oddU/eta 248 of 248 clean. Odds 75 : 25 (the runs may also hit the 10-minute cap — then «not measured», not a miss).
## Outcomes of S15–S18 (logs/author_*.log)

- **S15 HIT.** 16 380 / 8 001 / 393 120 / 360, all failures 0, controls True. The code confirms the reading: the penalty loop runs on every house, so 201 096 of the 393 120 «shifts» are zero vectors.
- **S16 HIT.** (A) 15 746 trials, 0 failures; (B) 0 failures; control 189 of 2 841, exactly as printed.
- **S17 HIT.** 69 cases, 0 bad; controls 42 and 26.
- **S18 HIT.** generic/rand 245 clean (bad: l = 63, c = 1, 2, 3); oddU/rand 169 clean (79 bad, first l = 32); generic/eta 248; oddU/eta 248. Each run under 70 s.

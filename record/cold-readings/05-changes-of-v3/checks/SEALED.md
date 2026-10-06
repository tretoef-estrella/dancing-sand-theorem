# SEALED predictions (before measuring)
Sealed at Mon Oct  5 18:43:44 CEST 2026, before writing or running any gate code. Odds are my honest probability that the prediction comes true.

S1. Every house H = (I, k, ℓ, α) with 1 ≤ k ≤ 7, α ≤ 3 (65 532 houses): fit(x_H) has only integral values. — 97 %.
S2. Every penalty cell with P_r, P_c ∈ [0, 4], k ≤ 6, α ≤ 3, and every deletion (ℓ = 2^k − 1, I ≠ ∅, k ≤ 7, α ≤ 3): integral fit. — 97 %.
S3. In every house with k ≤ 7, α ≤ 3 that has a boundary (a first dancer b with J_H(b) = 1), x_H is cut at b and at its mirror, and both cuts are strict. — 97 %.
S4. The raw clocks u_i(D) of §1.2, computed from §1.2 alone (φ, κ, h), for every family 1 ≤ λ ≤ 255 and every shift 0 ≤ i ≤ 40 (∞ excluded at i = 0): every level set of the antitonic fit has an integral mean. — 95 %.
S5. Proposition 5.3 / 5.4 identities, computed from §1.2 and §5–§7.3 definitions (u_i = k + K + κ(m,K) + x_D, x_D = penalty-cell clocks of H = (I,k,m mod K,1) with P_r = r_k(m), P_c = r_k(m+K); u_0 = k + K + x_{H♯}): 0 mismatches on the range of S4. — 96 %.
S6. Proposition 9.6 (H): for every real cell of S4 with i ≥ 1, the first level set of the fit is {D ⊆ P_l} for some l. — 93 %.
S7. Control C1 (must fire): x_H with 1 added at its first dancer (not a house) has a non-integral fit in a positive number of houses (k ≤ 6). — 95 %.
S8. Control C2 (must fire): random antisymmetric integer sequences of length 8 (entries in [−6, 6]) have a non-integral fit in at least 10 % of 10 000 trials. — 85 %.
S9. Control C3 (must fire): «strictness one dancer after the boundary» fails in a positive number of houses. — 92 %.
S10 (real risk). Among the real cells of S4 with i ≥ 1 and a boundary b, there is at least one whose head ends exactly at b (|head| = position of b) with that position NOT a power of 2 — i.e. a cell where a non-strict cut at b would have made the head non-dyadic. — 55 %.
S11 (real risk). There is a house with I ≠ ∅ and k ≤ 7 (α = 1) whose fit is identically 0 (one level set). — 70 %.
S12 (real risk). For α = 1 and k ≤ 7, the largest level set of fit(x_H) over all houses with I ≠ ∅ has length ≥ 2^{k−1} for some k ≥ 3 (central flats can be half the sequence or more). — 75 %.

Addendum sealed at Mon Oct  5 18:44:10 CEST 2026, still before running anything:
- While writing the code I saw that S10 is ill-posed: «head ends exactly at b» means head length = position of b, and S6 says the head length is a power of 2. So S10 can only come true if S6 fails. I keep S10 as sealed (it will be scored), and I record this as an error of design in REPORT §8.
S13 (replacement for the intent of S10). Counterfactual: in the real cells of S4 with i ≥ 1 and a boundary, move the jump of the penalty shift one dancer late (to position pos(b) + 1). Then in at least one cell the head of the shifted sequence is NOT dyadic. — 65 %.
S14. In the real cells of S4 with i ≥ 1 and a boundary, the position pos(b) is not a power of 2 in at least one cell (so a split of the head at b would not be dyadic). — 97 %.

Addendum 2, sealed at Mon Oct  5 18:46:03 CEST 2026, after the full run and before this measurement:
S15. In at least one real cell of S4 (i ≥ 1, with a boundary and P_r + P_c > 0), the head of the fit reaches a jump of the penalty shift (|head| ≥ min(pos(b), N − pos(b))). — 50 %.

## Scores (written after the runs; logs/gate_cold5_full.log, logs/head_vs_jump.log, both VIGIA-FIN-OK)
- S1 HIT (0 non-integral in 65 532 houses).
- S2 HIT (192 024 penalty cells, 741 deletions; 0 failures).
- S3 HIT (32 385 houses with a boundary; every cut present and strict).
- S4 HIT (10 455 real cells; 0 non-integral level sets of the raw clocks of §1.2).
- S5 HIT (0 mismatches, both identities).
- S6 HIT (10 200 cells with i ≥ 1; every head dyadic).
- S7 HIT (control fires: 1 942 of 16 380).
- S8 HIT (control fires: 3 299 of 10 000).
- S9 HIT (control fires: 7 967 of 30 078).
- S10 FAILED (0 hits) — ill-posed, as recorded before the run: it contradicts S6.
- S11 HIT (949 witnesses; the first ones are trivial: I = {0}).
- S12 HIT (witness I = {0,1}, k = 3, ℓ = 0: one level set of length 4 = 2^{k−1}).
- S13 FAILED (0 of 2 084). Badly designed: moving the jump one dancer LATER never enters the head, because the head always ends at or before the jump (S15).
- S14 HIT (1 734 of 2 572 cells with a boundary).
- S15 HIT (1 034 of 2 572 cells: the head ends exactly at a jump; it never goes past one).
Marker: 13 hits, 2 failures (S10 ill-posed, S13 ill-designed). Both failures are mine, in the design of the bets, not in the paper.

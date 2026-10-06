# Where to attack

We believe the proof is correct. If it is not, the error is most likely in one of the places below, and we would rather hear about it than be agreed with. This page names the load-bearing joints of [the paper](paper/THE_DANCING_SAND_THEOREM_v8.pdf) (version 8), in the order in which we would press on them, and says what has already been found there.

## 1. The floor: Theorem 7.8 (Theorem F) and the pooling (§7)

This is the longest combinatorial argument, and **the one gap ever found in the text was here**.
- In version 1, the integer part of **Lemma 7.2(b)** was false as stated. The counterexample is `x = (3, 4, 3, 4)`, cut at `2`, with `δ = (1, 1, 0, 0)`. It was used in step 1 of Theorem 7.8, in Lemma 7.9, in Theorem 7.10 and in what is now Proposition 9.6.
- No theorem was affected. Version 2 restated the lemma and made the cuts of Theorem 7.8 *strict*, with a proof. Cold reader 3 found the gap and proposed the repair, the auditor re-derived it, and cold reader 4 checked it ([record/cold-readings/03-paper-v1-whole/](record/cold-readings/03-paper-v1-whole/REPORT.md), [04-changes-of-v2/](record/cold-readings/04-changes-of-v2/REPORT.md)).
- Reader 4 also proved that the fit of every house is integral, so the rounding in the rule never acts (**Lemma 7.9**).

Press on:
- **the strict (Cut)** and its use at every boundary;
- **the penalty cells** of Lemma 7.5, and the shifts `P_r, P_c`;
- **the deletion at `i = 0`**, the case where the row `∅` of `M` is zero;
- **the price of the central flat** in the construction of `V`. Two prices one unit off are detected by the readers' controls in thousands of houses, so an off-by-one here would be fatal.

Machine checks: [checks/gate/gate_strict_cut.py](checks/gate/gate_strict_cut.py), [gate_sections5to7.py](checks/gate/gate_sections5to7.py), [gate_lemma72.py](checks/gate/gate_lemma72.py), and the readers' own engines in [record/cold-readings/](record/README.md). They find zero failures, but a check of finitely many houses is not a proof; the proof is the text.

## 2. The ceiling: Theorem 6.2 (Theorem O)

Exactly one golden bijection for every `r`; the proof is an induction on the top binary digit. A second bijection would break the upper bound.
- Look at the case `r > N/2`, where some rows have top bit `0`.
- Look at the identification of tails of `I` with blocks of top bits equal to `1`.
- The negative controls replace «golden» by «any subset» or «any run of digits», and the count is no longer `1` ([gate_theoremO.py](checks/gate/gate_theoremO.py)).
- The proof by top bits was new in the writing of version 1, so it was not part of the chains read cold before the text existed. It was read cold as text by reader 3, who re-derived it.

## 3. The dance and its closed form (§4)

- **Propositions 4.1 and 4.2** are Schur complements with a halving. Check the signs and the factor `½` in the couplings, and the lexicographic order of the slots after a split move.
- **Theorem 4.4** gives the closed form of the final matrix. The factor `2^{o(Δ)}` is load-bearing: without it the closed form differs from the dance in 420 of 420 cells and predicts a wrong Smith form in 262 ([gate_dance.py](checks/gate/gate_dance.py)).
- **Lemma 4.5 (the deficit law)** gives the valuations of the coefficients of the polynomial `q_k`.

## 4. The translation and the decomposition (§2–§3)

- **Lemma 2.2 (the dictionary)**: `σ = F + n − H` in the Kostant `ℤ`-form. The basis `s_S` is, up to the sign `(−1)^{|S|}`, the change of variables of Gao et al.; check the sign conventions.
- **Lemma 3.2 (Lemma W)** and **Theorem 3.6**: the decomposition into the lattices `T(λ)` is over `ℤ_2`, not only modulo `2`. It rests on an elementary lifting lemma for `SL_2` proved in the paper, on Weyl's theorem on complete reducibility over `ℚ`, and on the completeness of `ℤ_2` (Remark (2) after Theorem 3.6).
- **The multiplicities** `m_λ(n)` are checked against Larsen's fusion rule for `V^{⊗2}` at `p = 2` for even `n ≤ 64`.

## 5. The fold law (§10)

- **Theorem 10.12 (rigidity)** rests on one sentence: the Smith form of the final matrix is computed from its support and the valuations of its entries alone. That is what Lemma 6.1 and Theorem 6.2 see; press on whether anything else enters.
- **Theorem 10.15 (cleanliness)** says that the coefficients of every level stay in the ring `𝒦` of functions `a + 2χ(2y)`. Its hypotheses matter: Remark (2) of §10.5 records dances that are not clean when the weights are random. Lemma 10.13 uses Strassmann's theorem.
- **Theorem 10.16 at `c = 0`** uses `2`-adic continuity in the shift. Check that every operation of the dance is continuous, as the proof says: odd denominators and a unit pivot.
- **The even families:** the glue (Lemma 10.19) and the bend (Lemma 10.20), where the two sides of the fold law differ by a unit at the end of the dance.
- **The weights** `η_m`, `η'_m` are units by the von Staudt–Clausen theorem. They are checked for `m ≤ 39` ([gate_section10.py](checks/gate/gate_section10.py)).

## 6. What is quoted, and what is measured

- **Quoted:** classical results only — Weyl's theorem on complete reducibility over `ℚ` (in Lemma 3.3), Kummer's theorem, Legendre's formula, the von Staudt–Clausen theorem, Strassmann's theorem, Kostant's commutation formula, the pool-adjacent-violators algorithm. For the corollaries: Bai's odd part, and Gao et al.'s Proposition 1.9 for the odd part of the folded cube.
- **Measured, not proved, and not used in any proof:** the turned lid (§11, question 2), and Remark (2) of §10.5.

## How to report

Open an issue in this repository, or write to the author (tretoef@gmail.com). Please say which statement fails and give the smallest case, if you have one. Every correction will be credited.

---

[README](README.md) · [The theorems](THEOREMS.md) · [How to verify](HOW_TO_VERIFY.md)

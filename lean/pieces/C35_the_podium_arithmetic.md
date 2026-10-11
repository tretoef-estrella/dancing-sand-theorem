# C35 — The podium arithmetic (Lemma 9.2, Lemma 9.5, and parts (M), (K) of Proposition 9.6)

Piece C35 of the Lean formalization of «The Dancing Sand Theorem» (paper v8, §9.2). Folder `RequestProject/Podium/`, namespace `Podium`.

This piece is the arithmetic of §9.2: the clearings of a number and where `φ(y) = y + v_2(y)` is largest (Lemma 9.2), the carry bound (Lemma 9.5, «Lemma K»), and the two arithmetic steps (M) and (K) of the proof of Proposition 9.6 (the mean of the raw clocks over a dyadic head, and its bound). Propositions 9.3, 9.4 and step (H) of Proposition 9.6 (which use the fit machinery of §7) are a later piece.

## Setting (reused, not redefined)

- C3 (`Rulers`): `s2`, `v2`, `kappa`, `phi`, `oE`, `minOr`, `next`, `h`, `t1`, `hSum`, `lam`, `xi`, `clock`, `lemma_5_0_xi`, `proposition_5_3`.

Fix `k : ℕ` and `I : Finset ℕ` with `I ⊆ Finset.range k`; `K := 2 ^ k`, `s := I.card`. Note `Rulers.lam k I + 1 = 2 ^ k + Rulers.oE I`.

New definitions (encodings are free provided they are faithful):
- `psi k I E : ℤ := Σ_{t ∈ E} ((Rulers.h k I t : ℤ) − 2 ^ t)`  (`ψ(E)` of §5).
- `P I l : Finset ℕ` := the `l` smallest elements of `I` (recommended: `I.filter (fun t => (I.filter (· < t)).card < l)`); `P_l = {t_1, …, t_l}`.
- `tAt k I l : ℕ := Rulers.minOr k (I \ P I l)`  (`t_{l+1}`, with `t_{s+1} = k`).
- `Y k I l : ℕ := 2 ^ k + Rulers.oE (I \ P I l)`  (`Y_l = λ + 1 − o_{P_l}`).
- `clear N q : ℕ := 2 ^ q * (N / 2 ^ q)`  (`N` with its bits below `q` cleared).

## Part P — the prefixes

**(P0)** For `l ≤ s`: `P I l ⊆ I`, `(P I l).card = l`, every element of `P I l` is smaller than every element of `I \ P I l`; `P I 0 = ∅`, `P I s = I`; and `Y k I l + Rulers.oE (P I l) = Rulers.lam k I + 1`.

## Part L — Lemma 9.2

**(La)** For `l ≤ s`: `Rulers.phi (Rulers.lam k I + 1) + psi k I (P I l) = Rulers.phi (Y k I l)`; and `Rulers.v2 (Y k I l) = tAt k I l`.

*Sketch.* `ψ(P_l) = Σ_{j≤l}(t_{j+1} − t_j) − o_{P_l} = t_{l+1} − t_1 − o_{P_l}` (telescoping, `h_{t_j} = t_{j+1} − t_j`), `φ(λ + 1) = λ + 1 + t_1`, `φ(Y_l) = Y_l + t_{l+1}`.

**(Lb)** `clear N q ≤ N` for all `N, q`. For `N ≥ 1` and `1 ≤ y ≤ N` there is `q` with `1 ≤ clear N q` and `Rulers.phi y ≤ Rulers.phi (clear N q)`.

*Sketch.* With `q := v_2(y)`, `y` is a multiple of `2^q` not above `N`, so `y ≤ clear N q`, and `v_2(clear N q) ≥ q`.

**(Lc)** For `l ≤ s` there is `q` with `Y k I l = clear (Rulers.lam k I + 1) q`; for every `q` with `1 ≤ clear (Rulers.lam k I + 1) q` there is `l ≤ s` with `clear (Rulers.lam k I + 1) q = Y k I l`. If `1 ≤ s`: `Y k I l ≤ Y k I 1` for `1 ≤ l ≤ s`, and for every `q` with `1 ≤ clear (Y k I 1) q` there is `l` with `1 ≤ l ≤ s` and `clear (Y k I 1) q = Y k I l`.

**(Ld)** Consequently: for `1 ≤ y ≤ Rulers.lam k I + 1` there is `l ≤ s` with `Rulers.phi y ≤ Rulers.phi (Y k I l)`; and if `1 ≤ s`, for `1 ≤ y ≤ Y k I 1` there is `l` with `1 ≤ l ≤ s` and `Rulers.phi y ≤ Rulers.phi (Y k I l)`.

## Part K — Lemma 9.5 (Lemma K)

**(K)** For `a : ℕ`, `B ≥ 1` and `q : ℕ` there is `y` with `1 ≤ y`, `y ≤ 2 ^ q * (a + B)` and `Rulers.phi (2 ^ q * B) + Rulers.kappa a B ≤ Rulers.phi y`.

*Sketch.* If `κ(a, B) = 0`, `y = 2^q B`. Otherwise let the highest carry of `a + B` leave bit `p − 1`; then `κ ≤ p − v_2(B)`, `(a + B) mod 2^p < a mod 2^p ≤ a`, and `y := 2^q((a + B) − ((a + B) mod 2^p))` has `2^q(B + 1) ≤ y ≤ 2^q(a + B)` and `v_2(y) ≥ q + p`.

## Part M — steps (M) and (K) of the proof of Proposition 9.6

**(M1)** For `D ⊆ I` and `i ≥ 1`: `Rulers.clock k I i D = Rulers.phi (Rulers.lam k I + 1) + 2 * psi k I D + Rulers.kappa (i − 1) (2 ^ k + Rulers.oE (I \ D)) − Rulers.kappa (i − 1) (Rulers.oE D)`.

*Sketch.* Steps 1–2 of the proof of Proposition 5.3 (C3 `proposition_5_3`, `xi_facts`).

**(M2)** For `l ≤ s` and `i ≥ 1`:
`Σ_{D ∈ (P I l).powerset} Rulers.clock k I i D = Σ_{D ∈ (P I l).powerset} (Rulers.phi (Y k I l) + Rulers.kappa (i − 1) (Y k I l + Rulers.oE D) − Rulers.kappa (i − 1) (Rulers.oE D))`.

*Sketch.* Each digit of `P_l` lies in half the subsets, so `Σ 2ψ(D) = 2^l ψ(P_l)`; `φ(λ+1) + ψ(P_l) = φ(Y_l)` (La); `K + o_{I∖D} = Y_l + o_{P_l ∖ D}` and `D ↦ P_l ∖ D` permutes the subsets of `P_l`.

**(M3)** For `Y, o, m, q : ℕ` with `2 ^ q ∣ Y` and `o < 2 ^ q`:
`Rulers.kappa m (Y + o) − Rulers.kappa m o = Rulers.kappa (m / 2 ^ q + (if 2 ^ q ≤ m % 2 ^ q + o then 1 else 0)) (Y / 2 ^ q)`.

**(M4)** (step (K)) For `l ≤ s`, `D ⊆ P I l` and `m : ℕ` there is `y` with `1 ≤ y`, `y ≤ Rulers.lam k I + 1 + m` and `Rulers.phi (Y k I l) + Rulers.kappa m (Y k I l + Rulers.oE D) − Rulers.kappa m (Rulers.oE D) ≤ Rulers.phi y`.

*Sketch.* (M3) with `q = v_2(Y_l) = t_{l+1}` (`o_D < 2^q`), then (K) with `B = Y_l/2^q`, `a = m_h + c_D`: `Y_l + 2^q(m_h + c_D) ≤ Y_l + m + o_{P_l} = λ + 1 + m`.

**(M5)** For `l ≤ s`, `i ≥ 1` and `G : ℤ` with `Rulers.phi y ≤ G` for every `1 ≤ y ≤ Rulers.lam k I + 1 + (i − 1)`:
`Σ_{D ∈ (P I l).powerset} Rulers.clock k I i D ≤ 2 ^ l * G`.

## Notes

- Nothing is cited. In the cube, a family `λ` at shift `i` has `λ + 2i = n`, so `λ + 1 + (i − 1) = n − i` and (M5) is the bound «mean ≤ g(n − i + 1)» of Proposition 9.6 once its head is dyadic.
- Brute force (`chkC35.py`): (P), (La), (Lc), (M1), (M2), (M4) on every `k ≤ 7`, `I ⊆ [0,k)`, `i ≤ 8`, `D`; (Lb) on `N < 600`; (M3) on `Y < 200`, `q ≤ 5`, all `o`, `m < 300` step 7; (K) on `a < 70`, `1 ≤ B < 70`, `q ≤ 3`. Controls that fire: `φ(λ)` for `φ(λ+1)` in (La); «the maximum is at `N`» in (Lb); `ψ` without the factor `2` in (M1); the range `[1, λ + m]` in (M4).
